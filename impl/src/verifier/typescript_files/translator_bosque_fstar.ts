//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

// PRIORITIES:
// LoadFieldDefaultValue Not implemented yet
// MIRAccessConstantValue Not implemented yet
// MIRAccessFromField Not implemented yet
// MIRModifyWithFields Not implemented yetcat
// MIRIsTypeOfSome Not implemented yet
// ConstructorPrimaryCollectionSingletons Not implemented yet

import * as assert from "assert"
import * as FS from "fs";
import * as ChildProcess from "child_process"
import * as Path from "path"
import {
  MIRBasicBlock, MIRJumpCond, MIROp, MIROpTag, MIRVarStore, MIRRegisterArgument, MIRReturnAssign, MIRPhi, MIRBinCmp, MIRArgument,
  MIRBinOp, MIRPrefixOp, MIRBody, MIRConstructorTuple, MIRConstructorRecord, MIRInvokeFixedFunction, MIRIsTypeOfNone, MIRLoadFieldDefaultValue,
  MIRLoadConstTypedString, MIRLoadConst, MIRConstructorPrimary, MIRIsTypeOfSome, MIRVariable, MIRAccessFromIndex, MIRProjectFromIndecies,
  MIRAccessFromProperty,
  MIRProjectFromProperties,
  MIRModifyWithFields,
  MIRAccessFromField,
  MIRProjectFromFields,
  MIRConstructorPrimaryCollectionSingletons,
  MIRBinEq, MIRAccessConstantValue
} from "../../compiler/mir_ops";
import { computeBlockLinks, FlowLink } from "../../compiler/mir_info";
import { ExprExpr, ReturnExpr, AssignmentExpr, ConditionalExpr } from "./expression_expr";
import {
  IntType, BoolType, FuncType, TypeExpr, TupleType, TypedStringType, RecordType, UnionType, NoneType, AnyType, SomeType,
  ConstructorType, ParsableType, GUIDType, TruthyType, ObjectType, ListType
} from "./type_expr";
import { ConstTerm, VarTerm, FuncTerm, TermExpr, TupleTerm, TupleProjExpr, RecordTerm, RecordProjExpr, ListTerm } from "./term_expr";
import { sanitizeName, topologicalOrder } from "./util";
import { MIRInvokeBodyDecl, MIRAssembly, MIRConceptTypeDecl, MIREntityTypeDecl, MIRConstantDecl, MIRFieldDecl } from "../../compiler/mir_assembly";
  
import { printBosqueTypesFST } from "./bosqueTypesFST";
import { printBosqueTermsFST } from "./bosqueTermsFST";

type StringTypeMangleNameWithFkey = string;

class TranslatorBosqueFStar {

  static readonly any_type      = new AnyType();
  static readonly some_type     = new SomeType();
  static readonly truthy_type   = new TruthyType();
  static readonly none_type     = new NoneType();
  static readonly parsable_type = new ParsableType();
  static readonly bool_type     = new BoolType();
  static readonly int_type      = new IntType();
  static readonly guid_type     = new GUIDType();
  static readonly object_type   = new ObjectType();
  static readonly string_type   = new TypedStringType(TranslatorBosqueFStar.any_type);
  static readonly skip_command  = new VarTerm("_skip", TranslatorBosqueFStar.bool_type, "_global");
  static readonly DEBUGGING     = true;

  static fresh_count = 0;

  // String[MangledNamewithFkey] means that the string
  // takes into consideration the scope where it comes from
  // checked_types : String[MangledNamewithFkey] -> TypeExpr
  readonly checked_types:         Map<StringTypeMangleNameWithFkey, TypeExpr>;
  static   concept_declarations:  Map<string, MIRConceptTypeDecl>;
  static   entity_declarations:   Map<string, MIREntityTypeDecl>;
  readonly constant_declarations: Map<string, MIRConstantDecl>;
  readonly invoke_declarations:   Map<string, MIRInvokeBodyDecl>;
  readonly default_declarations:  Map<string, MIRFieldDecl>; 

  readonly is_fkey_declared: Set<string> = new Set<string>();
  readonly function_declarations = [] as FunctionDeclaration[];

  readonly file_name:             string;
  readonly fstar_files_directory: string;

  constructor(masm: MIRAssembly, file_name: string) {
    // Revelant information about masm
    // masm.typeMap: Map containing all the types used in the programs to analyze
    // masm.entityDecls: Map containing entities
    // masm.conceptDecls: Map containing concepts
    // masm.primitiveInvokeDecls: Map containing all the functions
    // used in the Bosque File from the Core and Collection library
    // masm.invokeDecls: Map containing function declarations
    // masm.fieldDecls: Map containing declaration about field (in concepts and entities as well)

    this.checked_types = new Map<StringTypeMangleNameWithFkey, TypeExpr>();

    TranslatorBosqueFStar.concept_declarations = masm.conceptDecls;
    TranslatorBosqueFStar.entity_declarations  = masm.entityDecls;
    this.constant_declarations                 = masm.constantDecls;
    this.invoke_declarations                   = masm.invokeDecls;

    // Define default_values as the non undefined value entries of
    // masm.fieldDecls
    this.default_declarations = new Map<StringTypeMangleNameWithFkey, MIRFieldDecl>();
    masm.fieldDecls.forEach((value, key) => {
      if(value.value !== undefined){
        this.default_declarations.set(key, value);
      }
    });

    // FIX: This is wrong, because these function should have
    // its actual FStar implementation. It's useful because
    // momentarily these functions have 'valid definitions'.
    masm.primitiveInvokeDecls.forEach((_, index) => {
      this.invoke_declarations.set(index, (this.invoke_declarations.get("NSMain::id") as MIRInvokeBodyDecl))
    });

    this.file_name             = file_name;
    this.fstar_files_directory = Path.join(Path.normalize(Path.join(__dirname, "../")), "/fstar_files").replace("bin", "src");
  }

  // Extract provide relation of user defined types
  extractProvidesRelation(declarations: Map<string, MIREntityTypeDecl | MIRConceptTypeDecl>): Map<string, Set<string>> {
    const nodes_neighbors = new Map<string, Set<string>>();

    declarations.forEach((value, index) => {
      if (!index.includes("NSCore")) {
        if (nodes_neighbors.get(index) == undefined) {
          nodes_neighbors.set(index, new Set<string>());
        }

        value.provides.map(x => {
          if (nodes_neighbors.get(x) == undefined) {
            nodes_neighbors.set(x, new Set<string>());
          }
          (nodes_neighbors.get(x) as Set<string>).add(index)
        });
      }
    });
    return nodes_neighbors;
  }

  serializeTypes(declarations: Map<string, MIREntityTypeDecl | MIRConceptTypeDecl>): Set<string> {
    const nodes_neighbors = this.extractProvidesRelation(declarations);
    return new Set(topologicalOrder(nodes_neighbors));
  }

  static debugging(message: string, flag: boolean): void {
    if (flag) {
      console.log(message);
    }
  }

  static optionalTupleSugaring(non_optionals: TypeExpr[], optionals: TypeExpr[]): UnionType {
    const set_of_types = new Set<TypeExpr>();
    // set_of_types.add(new TupleType(false, non_optionals));

    const num_optionals = optionals.length;
    for (let index = 0; index < num_optionals; ++index) {
      // Copy non_optionals
      let temp: TypeExpr[] = [];
      for (let i = 0; i < non_optionals.length; ++i) {
        temp.push(non_optionals[i]);
      }
      // Copy optionals
      for (let i = 0; i < index; ++i) {
        temp.push(optionals[i]);
      }
      set_of_types.add(new TupleType(false, temp));
    }

    return new UnionType(set_of_types);
  }

  static optionalRecordSugaring(non_optional_properties: string[], non_optional_types: TypeExpr[], 
    optional_properties: string[], optional_types: TypeExpr[]): UnionType {
      const set_of_types = new Set<TypeExpr>();

      const total = Math.pow(2, optional_properties.length);
      for (let i = 0; i < total; i++) {

        let temp_set_properties: string[] = [];
        let temp_set_types: TypeExpr[] = [];

        // Copy non_optionals
        for (let i = 0; i < non_optional_properties.length; ++i) {
          temp_set_properties.push(non_optional_properties[i]);
          temp_set_types.push(non_optional_types[i])
        }

        let num = i.toString(2);
        while (num.length < optional_properties.length) {
          num = '0' + num;
        }
        for (let b = 0; b < num.length; b++) {
          if (num[b] === '1') {
            // Copy optionals
            temp_set_properties.push(optional_properties[b]);
            temp_set_types.push(optional_types[b]);
          }
        }
        const entries_temp = temp_set_properties.map((value, index) => [value, temp_set_types[index]]) as [string, TypeExpr][];
        entries_temp.sort((x, y) => x[0].localeCompare(y[0]))
        set_of_types.add(new RecordType(false, entries_temp.map(x => x[0]), entries_temp.map(x => x[1])));
      }

      return new UnionType(set_of_types);
    }

  // TOUPDATE: Add more types as needed
  // String[Type] means that the string is a type which 
  // description comes from a Type expression
  // stringVarToTypeExpr : String[Type] -> TypeExpr
  static stringVarToTypeExpr(s: string): TypeExpr {
    switch (s) {
      case "NSCore::Any": {
        return TranslatorBosqueFStar.any_type;
      }
      case "NSCore::Some": {
        return TranslatorBosqueFStar.some_type;
      }
      case "NSCore::Truthy": {
        return TranslatorBosqueFStar.truthy_type;
      }
      case "NSCore::None": {
        return TranslatorBosqueFStar.none_type;
      }
      case "NSCore::Parsable": {
        return TranslatorBosqueFStar.parsable_type;
      }
      case "NSCore::Bool": {
        return TranslatorBosqueFStar.bool_type;
      }
      case "NSCore::Int": {
        return TranslatorBosqueFStar.int_type;
      }
      case "NSCore::GUID": {
        return TranslatorBosqueFStar.guid_type;
      }
      case "NSCore::Object": {
        return TranslatorBosqueFStar.object_type;
      }
      default: {
        // Concept
        if (TranslatorBosqueFStar.concept_declarations.has(s) && !s.includes("NSCore")) {
          const description = TranslatorBosqueFStar.concept_declarations.get(s) as MIRConceptTypeDecl;
          return new ConstructorType(description.tkey,
            description.fields.map(x => [x.name, TranslatorBosqueFStar.stringVarToTypeExpr(x.declaredType)]) as [string, TypeExpr][]);
        }
        // Entities
        if (TranslatorBosqueFStar.entity_declarations.has(s) && !s.includes("NSCore")) {
          const description = TranslatorBosqueFStar.entity_declarations.get(s) as MIREntityTypeDecl;
          return new ConstructorType(description.tkey,
            description.fields.map(x => [x.name, TranslatorBosqueFStar.stringVarToTypeExpr(x.declaredType)]) as [string, TypeExpr][]);
        }
        // Tuple
        if (s.charAt(0) == '[') {
          s = s.slice(1, -1);
          let is_open = false;
          // Open Tuple check
          if (s.includes("...")) {
            s = s.slice(0, -5); // Getting rid of the ellipsis and comma
            is_open = true;
          }
          if (s.includes("?:")) {
            // This is based on the assumption that 
            // concrete types cannot follow optional types
            // inside tuples
            const types = s.split("?:");
            const non_optionals = types[0];
            const optionals = types.slice(1);
            if (non_optionals.length == 0) {
              return this.optionalTupleSugaring([],
                optionals.map(x => x.includes(",") ? x.slice(0, -2) : x).map(TranslatorBosqueFStar.stringVarToTypeExpr));
            }
            else {
              return this.optionalTupleSugaring(non_optionals.slice(0, -2).split(", ").map(TranslatorBosqueFStar.stringVarToTypeExpr),
                optionals.map(x => x.includes(",") ? x.slice(0, -2) : x).map(TranslatorBosqueFStar.stringVarToTypeExpr));
            }
          }
          else {
            return new TupleType(is_open, s.split(", ").map(TranslatorBosqueFStar.stringVarToTypeExpr));
          }
        }
        // Record
        if (s.charAt(0) == '{') {
          s = s.slice(1, -1);
          let is_open = false;
          // Open Record check
          if (s.includes("...")) {
            s = s.slice(0, -5); // Getting rid of the ellipsis and comma
            is_open = true;
          }
          const entries = s.split(", ");
          if (s.includes("?:")) {
            // This is based on the assumption that 
            // concrete types cannot follow optional types
            // inside tuples

            const non_optional_entries = entries.filter(x => !x.includes("?:"));
            const optional_entries = entries.filter(x => x.includes("?:"));
            const non_optional_field_names = non_optional_entries.map(x => x.substring(0, x.indexOf(":")));
            const optional_field_names = optional_entries.map(x => x.substring(0, x.indexOf("?:")));
            const non_optional_types = non_optional_entries.map(x => x.substring(x.indexOf(":") + 1)).map(TranslatorBosqueFStar.stringVarToTypeExpr);
            const optional_types = optional_entries.map(x => x.substring(x.indexOf("?:") + 2)).map(TranslatorBosqueFStar.stringVarToTypeExpr);

            return this.optionalRecordSugaring(non_optional_field_names, non_optional_types, optional_field_names, optional_types);
          }
          else {
            const field_names = entries.map(x => x.substring(0, x.indexOf(":")));
            const types = entries.map(x => x.substring(x.indexOf(":") + 1)).map(TranslatorBosqueFStar.stringVarToTypeExpr);
            return new RecordType(is_open, field_names, types);
          }
        }
        // Union
        if (s.includes("|")) {
          return new UnionType(new Set(s
            .split(" | ")
            .map(TranslatorBosqueFStar.stringVarToTypeExpr)
          ));
        }
        // Typed String 
        if (s.includes("NSCore::String")) {
          const index = s.indexOf("=");
          // This branch handles untyped strings
          if (index == -1) {
            return TranslatorBosqueFStar.string_type;
          }
          // This branch handles typed strings
          else {
            s = s.substr(index + 1, s.length - index - 2);
            return new TypedStringType(TranslatorBosqueFStar.stringVarToTypeExpr(s));
          }

        }
        console.log(s);
        console.log(`------ ERROR: Unknown type ${s} found while executing stringVarToTypeExpr ------`);
        throw new Error("------ ERROR: Unknown typed found while executin stringVarToTypeExpr ------");
      }
    }
  }

  // String[ValueType] means that the string is a type which
  // description comes from a Value expression
  // stringConstToTypeExpr : String[ValueType] -> TypeExpr
  static stringConstToTypeExpr(s: string): TypeExpr {
    let string_const = s.slice(1);
    string_const = string_const.substr(0, string_const.indexOf("="));
    switch (string_const) {
      case "none": {
        return TranslatorBosqueFStar.none_type;
      }
      case "int": {
        return TranslatorBosqueFStar.int_type;
      }
      case "true": {
        return TranslatorBosqueFStar.bool_type;
      }
      case "false": {
        return TranslatorBosqueFStar.bool_type;
      }
      case "string": {
        return TranslatorBosqueFStar.string_type;
      }
      default: {
        console.log("The case " + string_const + " is not implemented yet");
        throw new Error("The case " + string_const + " is not implemented yet");
      }
    }
  }

  // Given a MIRArgument, this function returns a TermExpr.
  // -) If the MIRArgument is a 'variable'
  // --) If the MIRArgument 'hasn't been recorded before', then the user
  // is supposed to use this method providing a TypeExpr, and the method
  // will add this MIRArgument to the checked_types collection.
  // --) If the MIIArgument 'has been recorded before', then the user
  // is supposed to pass undefined in ty, and the method will give back a
  // TermExpr by looking up the collection checked_types
  // -) If the MIRArgument is a 'constant', we rely on the stringify method
  // to make it work
  // The fkey string helps to keep track the function where the variable came 
  // from
  MIRArgumentToTermExpr(arg: MIRArgument | string, fkey: string, ty: TypeExpr | undefined): TermExpr {
    // This branch handles string names
    // These encode fresh names
    if (typeof arg === "string") {
      if(ty instanceof TypeExpr){
        const m_ty = ty as TypeExpr;
        this.checked_types.set(sanitizeName(fkey + arg), m_ty);
        return new VarTerm(sanitizeName(arg), m_ty, fkey);
      }
      else{
        return new VarTerm(sanitizeName(arg), this.checked_types.get(sanitizeName(fkey + arg)) as TypeExpr, fkey);
      }
    }
    // This branch handles variables
    if (arg instanceof MIRRegisterArgument) {
      if (ty instanceof TypeExpr) {
        this.checked_types.set(sanitizeName(fkey + arg.nameID), ty);
        return new VarTerm(sanitizeName(arg.nameID), ty, fkey);
      }
      else {
        return new VarTerm(sanitizeName(arg.nameID), this.checked_types.get(sanitizeName(fkey + arg.nameID)) as TypeExpr, fkey);
      }
    }
    // This branch handles constants
    else {
      return new ConstTerm(arg.stringify(), TranslatorBosqueFStar.stringConstToTypeExpr(arg.nameID), fkey);
    }
  }

  // MIRArgumentToTypeExpr : MIRArgument -> TypeExpr
  MIRArgumentToTypeExpr(arg: MIRArgument | string, fkey: string): TypeExpr {
    if(typeof arg === "string"){ 
      return (this.checked_types.get(fkey + arg) as TypeExpr);
    }
    // This branch handles variables
    if (arg instanceof MIRRegisterArgument) {
      return (this.checked_types.get(sanitizeName(fkey + arg.nameID)) as TypeExpr);
    }
    // This branch handles constants
    else {
      return TranslatorBosqueFStar.stringConstToTypeExpr(arg.nameID);
    }
  }

  opToAssignment(op: MIROp, comingFrom: string, fkey: string): [VarTerm, TermExpr] | [VarTerm, TermExpr][] {
    switch (op.tag) {
      case MIROpTag.MIRLoadConst: {
        const opLoadConst = op as MIRLoadConst;
        console.log(opLoadConst);
        const second_equal_sign_position = opLoadConst.src.nameID.indexOf("=", 1);
        const name_length = opLoadConst.src.nameID.length;
        const value_type = opLoadConst.src.nameID.slice(1, second_equal_sign_position - name_length);
        let value: string;
        if (value_type == "int" || value_type == "string") {
          value = opLoadConst.src.nameID.slice(second_equal_sign_position + 1);
        }
        else {
          value = value_type;
        }
        return [this.MIRArgumentToTermExpr(opLoadConst.trgt, fkey, TranslatorBosqueFStar.stringConstToTypeExpr(opLoadConst.src.nameID)),
          new ConstTerm(value, TranslatorBosqueFStar.stringConstToTypeExpr(opLoadConst.src.nameID), fkey)];
      }

      case MIROpTag.MIRLoadConstTypedString: {
        const opMIRLoadConstTypedString = op as MIRLoadConstTypedString;
        const current_tkey = opMIRLoadConstTypedString.tkey;
        const partial_decl = TranslatorBosqueFStar.entity_declarations.get(current_tkey);
        let current_type: ConstructorType;

        if (partial_decl == undefined) {
          const actual_decl = TranslatorBosqueFStar.concept_declarations.get(current_tkey) as MIRConceptTypeDecl;
          current_type = new ConstructorType(actual_decl.tkey,
            actual_decl.fields.map(x => [x.name, TranslatorBosqueFStar.stringVarToTypeExpr(x.declaredType)]) as [string, TypeExpr][]);
        }
        else {
          current_type = new ConstructorType(partial_decl.tkey,
            partial_decl.fields.map(x => [x.name, TranslatorBosqueFStar.stringVarToTypeExpr(x.declaredType)]) as [string, TypeExpr][]);
        }

        return [
          this.MIRArgumentToTermExpr(opMIRLoadConstTypedString.trgt, fkey, new TypedStringType(current_type)),
          new ConstTerm("\"" + opMIRLoadConstTypedString.ivalue.slice(1, -1) + "\"", new TypedStringType(current_type), fkey)
        ];
      }

      case MIROpTag.MIRLoadFieldDefaultValue: { 
        const opLoadFieldDefaultValue = op as MIRLoadFieldDefaultValue;

        return [
          this.MIRArgumentToTermExpr(
            opLoadFieldDefaultValue.trgt, fkey, 
            this.MIRArgumentToTypeExpr(sanitizeName(opLoadFieldDefaultValue.fkey), "")
          ), 
          this.MIRArgumentToTermExpr(opLoadFieldDefaultValue.fkey, "", undefined)
        ]
      }

      case MIROpTag.MIRConstructorPrimary: {
        const opConstructorPrimary = op as MIRConstructorPrimary;
        // BUG?: It seems the args in
        // opConstructorPrimary (i.e. a MIRConstructorPrimary)
        // are not presented in the order of fields in the 
        // respective MIREntityTypeDecl
        const current_tkey = opConstructorPrimary.tkey
        const current_entity_decl = TranslatorBosqueFStar.entity_declarations.get(current_tkey) as MIREntityTypeDecl;
        // To check/study the bug/enable the following console.logs
        //console.log("----opConstructorPrimary");
        //console.log(opConstructorPrimary);
        //console.log("----current_entity_decl");
        //console.log(current_entity_decl);
        //current_entity_decl.fields.map(x => { console.log(x.sourceLocation); } );
        //console.log("----this.checked_types");
        //console.log(this.checked_types);
        const field_types = current_entity_decl.fields.map(
          x => [x.name, TranslatorBosqueFStar.stringVarToTypeExpr(x.declaredType)]
        ) as [string, TypeExpr][];
        const assignments = opConstructorPrimary.args.map(
          (x, index) => [
            this.MIRArgumentToTermExpr(
              new MIRVariable(opConstructorPrimary.trgt.nameID + "_arg_" + index), 
              fkey, 
              this.MIRArgumentToTypeExpr(x, fkey)
            ), 
            this.MIRArgumentToTermExpr(x, fkey, undefined)
          ]
        ) as [VarTerm, TermExpr][];

        assignments.unshift([
          this.MIRArgumentToTermExpr(opConstructorPrimary.trgt, fkey, new ConstructorType(current_tkey, field_types)),
          new FuncTerm("B" + sanitizeName(current_tkey), assignments.map(x => x[0]), new ConstructorType(current_tkey, field_types), fkey)
        ]);
        return assignments;
      }



      // ---------------------------------------------------------------------------------------------------
      case MIROpTag.MIRConstructorPrimaryCollectionEmpty: { // IMPLEMENT:
        TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionEmpty Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
        return [new VarTerm("_ConstructorPrimaryCollectionEmpty", TranslatorBosqueFStar.int_type, fkey), new ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
      }
      // ---------------------------------------------------------------------------------------------------

      case MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
        const opConstructorPrimaryCollectionsSingletons = op as MIRConstructorPrimaryCollectionSingletons;

        const current_tkey = opConstructorPrimaryCollectionsSingletons.tkey.slice(opConstructorPrimaryCollectionsSingletons.tkey.indexOf("=") + 1, -1);
        const content_type = TranslatorBosqueFStar.stringVarToTypeExpr(current_tkey);

        const assignments = opConstructorPrimaryCollectionsSingletons.args.map((x, index) =>
          [this.MIRArgumentToTermExpr(new MIRVariable(opConstructorPrimaryCollectionsSingletons.trgt.nameID + "_arg_" + index), fkey, this.MIRArgumentToTypeExpr(x, fkey))
            , this.MIRArgumentToTermExpr(x, fkey, undefined)]) as [VarTerm, TermExpr][];

        assignments.unshift([this.MIRArgumentToTermExpr(opConstructorPrimaryCollectionsSingletons.trgt, fkey, new ListType(content_type)),
          new ListTerm(assignments.map(x => x[0]), content_type, fkey)
        ]);

        return assignments;
      }



      // ---------------------------------------------------------------------------------------------------
      case MIROpTag.MIRConstructorPrimaryCollectionCopies: { // IMPLEMENT:
        TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionCopies Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
        return [new VarTerm("_ConstructorPrimaryCollectionCopies", TranslatorBosqueFStar.int_type, fkey), new ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
      }
      case MIROpTag.MIRConstructorPrimaryCollectionMixed: { // IMPLEMENT:
        TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionMixed Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
        return [new VarTerm("_ConstructorPrimaryCollectionMixed", TranslatorBosqueFStar.int_type, fkey), new ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
      }
      // ---------------------------------------------------------------------------------------------------



      case MIROpTag.MIRConstructorTuple: {
        const opConstructorTuple = op as MIRConstructorTuple;
        const types = opConstructorTuple.args.map(x => this.MIRArgumentToTypeExpr(x, fkey));
        const elements = opConstructorTuple.args.map(x => this.MIRArgumentToTermExpr(x, fkey, undefined));
        return [this.MIRArgumentToTermExpr(opConstructorTuple.trgt, fkey, new TupleType(false, types)),
          new TupleTerm(elements, fkey)];
      }

      case MIROpTag.MIRConstructorRecord: {
        const opConstructorRecord = op as MIRConstructorRecord;
        const field_names = opConstructorRecord.args.map(x => x[0]);
        const types_of_elements = opConstructorRecord.args.map(x => this.MIRArgumentToTypeExpr(x[1], fkey));
        const elements = opConstructorRecord.args.map(x => this.MIRArgumentToTermExpr(x[1], fkey, undefined));
        return [this.MIRArgumentToTermExpr(opConstructorRecord.trgt, fkey, new RecordType(false, field_names, types_of_elements)),
          new RecordTerm(field_names, elements, fkey)];
      }
        
      case MIROpTag.MIRInvokeFixedFunction: {
        const opCallNamespaceFunction = op as MIRInvokeFixedFunction;
        const currentFunctionKey = opCallNamespaceFunction.mkey;
        console.log("hey");
        console.log(currentFunctionKey);
        // The following line will keep pushing to 
        // the stack_expressions stack

        this.collectExpr(currentFunctionKey);
        const resultType = TranslatorBosqueFStar.stringVarToTypeExpr((this.invoke_declarations.get(currentFunctionKey) as MIRInvokeBodyDecl).resultType);

        return [this.MIRArgumentToTermExpr(opCallNamespaceFunction.trgt, fkey, resultType),
          new FuncTerm(sanitizeName(currentFunctionKey),
            opCallNamespaceFunction.args.map(x => this.MIRArgumentToTermExpr(x, fkey, undefined)),
            resultType, fkey)];
      }
        
      case MIROpTag.MIRAccessFromIndex: {
        const opAccessFromIndex = op as MIRAccessFromIndex;
        const dimension = (this.MIRArgumentToTypeExpr(opAccessFromIndex.arg, fkey) as TupleType).elements.length;

        return [
          this.MIRArgumentToTermExpr(opAccessFromIndex.trgt, fkey, TranslatorBosqueFStar.stringVarToTypeExpr(opAccessFromIndex.resultAccessType)),
          new TupleProjExpr(opAccessFromIndex.idx, dimension,
            this.MIRArgumentToTermExpr(opAccessFromIndex.arg, fkey, undefined),
            TranslatorBosqueFStar.stringVarToTypeExpr(opAccessFromIndex.resultAccessType), fkey)
        ];
      }

      case MIROpTag.MIRProjectFromIndecies: {
        const opProjectFromIndecies = op as MIRProjectFromIndecies;
        const arg_dimension = (this.MIRArgumentToTypeExpr(opProjectFromIndecies.arg, fkey) as TupleType).elements.length;
        const actual_type_array = opProjectFromIndecies.resultProjectType.slice(1, -1).split(", ");

        const projected_args = opProjectFromIndecies.indecies.map((value, index) => [
          this.MIRArgumentToTermExpr("__fresh_name" + (TranslatorBosqueFStar.fresh_count + index), fkey, TranslatorBosqueFStar.stringVarToTypeExpr(actual_type_array[index])),
          new TupleProjExpr(value, arg_dimension,
            this.MIRArgumentToTermExpr(opProjectFromIndecies.arg, fkey, undefined),
            TranslatorBosqueFStar.stringVarToTypeExpr(actual_type_array[index]), fkey)
        ]) as [VarTerm, TermExpr][];

        TranslatorBosqueFStar.fresh_count += projected_args.length;

        const lhs_term = this.MIRArgumentToTermExpr(opProjectFromIndecies.trgt, fkey, TranslatorBosqueFStar.stringVarToTypeExpr(opProjectFromIndecies.resultProjectType));
        const rhs_term = new TupleTerm(projected_args.map(x => x[0]), fkey);

        projected_args.unshift([lhs_term, rhs_term]);

        return projected_args;
      }
        
      case MIROpTag.MIRAccessFromProperty: {
        const opAccessFromProperty = op as MIRAccessFromProperty;
        const dimension = (this.MIRArgumentToTypeExpr(opAccessFromProperty.arg, fkey) as RecordType).elements.length;

        return [
          this.MIRArgumentToTermExpr(opAccessFromProperty.trgt, fkey, TranslatorBosqueFStar.stringVarToTypeExpr(opAccessFromProperty.resultAccessType)),
          new RecordProjExpr(opAccessFromProperty.property, dimension,
            this.MIRArgumentToTermExpr(opAccessFromProperty.arg, fkey, undefined),
            TranslatorBosqueFStar.stringVarToTypeExpr(opAccessFromProperty.resultAccessType), fkey)
        ];
      }
        
      case MIROpTag.MIRProjectFromProperties: {
        const opProjectFromIndecies = op as MIRProjectFromProperties;
        const arg_dimension = (this.MIRArgumentToTypeExpr(opProjectFromIndecies.arg, fkey) as RecordType).elements.length;
        const actual_type_array = opProjectFromIndecies.resultProjectType.slice(1, -1).split(", ").map(x => {
          const index = x.indexOf(":") + 1;
          return x.substring(index);
        });

        const projected_args = opProjectFromIndecies.properties.map((value, index) => [
          this.MIRArgumentToTermExpr("__fresh_name" + (TranslatorBosqueFStar.fresh_count + index), fkey, TranslatorBosqueFStar.stringVarToTypeExpr(actual_type_array[index])),
          new RecordProjExpr(value, arg_dimension,
            this.MIRArgumentToTermExpr(opProjectFromIndecies.arg, fkey, undefined),
            TranslatorBosqueFStar.stringVarToTypeExpr(actual_type_array[index]), fkey)
        ]) as [VarTerm, TermExpr][];

        const lhs_term = this.MIRArgumentToTermExpr(opProjectFromIndecies.trgt, fkey, TranslatorBosqueFStar.stringVarToTypeExpr(opProjectFromIndecies.resultProjectType));
        const rhs_term = new RecordTerm(opProjectFromIndecies.properties, projected_args.map(x => x[0]), fkey);

        projected_args.unshift([lhs_term, rhs_term]);
        return projected_args;
      }

      case MIROpTag.MIRAccessFromField: {
        const opAccessFromField = op as MIRAccessFromField;

        const last_index_point = opAccessFromField.field.lastIndexOf(".");
        const field_name = opAccessFromField.field.substr(last_index_point + 1);
        const type_src = (this.checked_types.get(sanitizeName(fkey + opAccessFromField.arg.nameID)) as ConstructorType);
        const scope_name = sanitizeName(type_src.original_name);

        return [this.MIRArgumentToTermExpr(opAccessFromField.trgt, fkey, TranslatorBosqueFStar.stringVarToTypeExpr(opAccessFromField.resultAccessType)),
          new FuncTerm(`projectB${scope_name}_${field_name}`,
            [this.MIRArgumentToTermExpr(opAccessFromField.arg, fkey, undefined)],
            TranslatorBosqueFStar.stringVarToTypeExpr(opAccessFromField.resultAccessType), fkey)
        ];
      }

      case MIROpTag.MIRProjectFromFields: {
        const opProjectFromFields = op as MIRProjectFromFields;

        const actual_type_array = opProjectFromFields.resultProjectType.slice(1, -1).split(", ").map(x => {
          const index = x.indexOf(":") + 1;
          return x.substring(index);
        });
        const type_src = (this.checked_types.get(sanitizeName(fkey + opProjectFromFields.arg.nameID)) as ConstructorType);
        const scope_name = sanitizeName(type_src.original_name);

        const properties = opProjectFromFields.fields.map((value, _) => {
          const last_index_point = value.lastIndexOf(".");
          return value.substr(last_index_point + 1)
        });

        const projected_args = opProjectFromFields.fields.map((_, index) => {
          return [
            this.MIRArgumentToTermExpr("__fresh_name" + (TranslatorBosqueFStar.fresh_count + index),
              fkey, TranslatorBosqueFStar.stringVarToTypeExpr(actual_type_array[index])),

            new FuncTerm(`projectB${scope_name}_${properties[index]}`,
              [this.MIRArgumentToTermExpr(opProjectFromFields.arg, fkey, undefined)],
              TranslatorBosqueFStar.stringVarToTypeExpr(actual_type_array[index]), fkey)
          ]
        }) as [VarTerm, TermExpr][];

        TranslatorBosqueFStar.fresh_count += projected_args.length;

        const lhs_term = this.MIRArgumentToTermExpr(opProjectFromFields.trgt, fkey, TranslatorBosqueFStar.stringVarToTypeExpr(opProjectFromFields.resultProjectType));
        const rhs_term = new RecordTerm(properties, projected_args.map(x => x[0]), fkey);
        projected_args.unshift([lhs_term, rhs_term]);

        return projected_args;
      }




      // ---------------------------------------------------------------------------------------------------
      case MIROpTag.MIRProjectFromTypeTuple: { // IMPLEMENT:
        TranslatorBosqueFStar.debugging("MIRProjectFromTypeTuple Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
        return [new VarTerm("_MIRProjectFromTypeTuple", TranslatorBosqueFStar.int_type, fkey), new ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
      }
      case MIROpTag.MIRProjectFromTypeRecord: { // IMPLEMENT:
        TranslatorBosqueFStar.debugging("MIRProjectFromTypeRecord Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
        return [new VarTerm("_MIRProjectFromTypeRecord", TranslatorBosqueFStar.int_type, fkey), new ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
      }
      case MIROpTag.MIRModifyWithIndecies: { // IMPLEMENT:
        TranslatorBosqueFStar.debugging("MIRModifyWithIndecies Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
        return [new VarTerm("_MIRModifyWithIndecies", TranslatorBosqueFStar.int_type, fkey), new ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
      }
      case MIROpTag.MIRModifyWithProperties: { // IMPLEMENT:
        TranslatorBosqueFStar.debugging("MIRModifyWithProperties Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
        return [new VarTerm("_MIRModifyWithProperties", TranslatorBosqueFStar.int_type, fkey), new ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
      }
      case MIROpTag.MIRModifyWithFields: { // IMPLEMENT:
        const opModifyWithFields = op as MIRModifyWithFields;
        console.log(opModifyWithFields);

        return [new VarTerm("_MIRModifyWithFields", TranslatorBosqueFStar.int_type, fkey), new ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
      }
      case MIROpTag.MIRStructuredExtendTuple: { // IMPLEMENT:
        TranslatorBosqueFStar.debugging("MIRStructuredExtendedTuple Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
        return [new VarTerm("_MIRStructuredExtendTuple", TranslatorBosqueFStar.int_type, fkey), new ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
      }
      case MIROpTag.MIRStructuredExtendRecord: { // IMPLEMENT:
        TranslatorBosqueFStar.debugging("MIRStructuredExtendRecord Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
        return [new VarTerm("_MIRStructuredExtendRecord", TranslatorBosqueFStar.int_type, fkey), new ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
      }
      case MIROpTag.MIRStructuredExtendObject: { // IMPLEMENT:
        TranslatorBosqueFStar.debugging("MIRStructuredExtendObject Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
        return [new VarTerm("_MIRStructuredExtendObject", TranslatorBosqueFStar.int_type, fkey), new ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
      }
      case MIROpTag.MIRInvokeVirtualTarget: { // IMPLEMENT:
        TranslatorBosqueFStar.debugging("MIRInvokeVirtualTarget Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
        return [new VarTerm("_MIRInvokeVirtualTarget", TranslatorBosqueFStar.int_type, fkey), new ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
      }
      // ---------------------------------------------------------------------------------------------------

      case MIROpTag.MIRPrefixOp: {
        const opPrefixOp = op as MIRPrefixOp;
        return [this.MIRArgumentToTermExpr(opPrefixOp.trgt, fkey, this.MIRArgumentToTypeExpr(opPrefixOp.arg, fkey)),
          new FuncTerm(TermExpr.unary_op_to_fstar.get(opPrefixOp.op) as string,
            [this.MIRArgumentToTermExpr(opPrefixOp.arg, fkey, undefined)],
            this.MIRArgumentToTypeExpr(opPrefixOp.arg, fkey), fkey)];
      }

      case MIROpTag.MIRBinOp: {
        const opBinOp = op as MIRBinOp;
        const lhs = this.MIRArgumentToTermExpr(opBinOp.lhs, fkey, undefined);
        const rhs = this.MIRArgumentToTermExpr(opBinOp.rhs, fkey, undefined);
        return [this.MIRArgumentToTermExpr(opBinOp.trgt, fkey, TranslatorBosqueFStar.int_type),
          new FuncTerm(TermExpr.bin_op_to_fstar.get(opBinOp.op) as string,
            [lhs, rhs],
            TranslatorBosqueFStar.int_type, fkey)];
      }

      case MIROpTag.MIRBinEq: {
        const opBinEq = op as MIRBinEq;
        const lhs = this.MIRArgumentToTermExpr(opBinEq.lhs, fkey, undefined);
        const rhs = this.MIRArgumentToTermExpr(opBinEq.rhs, fkey, undefined);
        return [
          this.MIRArgumentToTermExpr(opBinEq.trgt, fkey, TranslatorBosqueFStar.bool_type),
          new FuncTerm("op_eqTerm", [lhs, rhs], TranslatorBosqueFStar.bool_type, fkey)
        ];
      }

      case MIROpTag.MIRBinCmp: { // DOUBLE CHECK regarding strings
        // The predicate returned is of type Bool
        // because the operations to arrive at this
        // point are <, <=, >, >= only
        const opBinCmp = op as MIRBinCmp;
        const lhs = this.MIRArgumentToTermExpr(opBinCmp.lhs, fkey, undefined);
        const rhs = this.MIRArgumentToTermExpr(opBinCmp.rhs, fkey, undefined);
        // Q: Is still necessary to check if the type is either
        // an int or a string?
        // A: Yes, because that will tell which `operation code` should be used
        // TODO: Implement the above
        return [this.MIRArgumentToTermExpr(opBinCmp.trgt, fkey, TranslatorBosqueFStar.bool_type),
          new FuncTerm((TermExpr.bin_op_to_fstar.get(opBinCmp.op) as string), [lhs, rhs], TranslatorBosqueFStar.bool_type, fkey)];
        // return [this.MIRArgumentToTermExpr(opBinCmp.trgt, fkey, TranslatorBosqueFStar.bool_type),
        //     new FuncTerm("extractBool",
        //         [new FuncTerm((TermExpr.binOpToFStar.get(opBinCmp.op) as string), [lhs, rhs], TranslatorBosqueFStar.bool_type, fkey)],
        //         TranslatorBosqueFStar.bool_type, fkey)];
      }





      // ---------------------------------------------------------------------------------------------------
      case MIROpTag.MIRRegAssign: { // IMPLEMENT:
        TranslatorBosqueFStar.debugging("MIRRegAssign Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
        return [new VarTerm("_MIRRegAssign", TranslatorBosqueFStar.int_type, fkey), new ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
      }
      case MIROpTag.MIRTruthyConvert: { // IMPLEMENT:
        TranslatorBosqueFStar.debugging("MIRTruthyConvert Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
        return [new VarTerm("_MIRTruthyConvert", TranslatorBosqueFStar.int_type, fkey), new ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
      }
      // ---------------------------------------------------------------------------------------------------






      case MIROpTag.MIRVarStore: {
        const opVarStore = op as MIRVarStore;
        return [this.MIRArgumentToTermExpr(opVarStore.name, fkey, this.MIRArgumentToTypeExpr(opVarStore.src, fkey)),
          this.MIRArgumentToTermExpr(opVarStore.src, fkey, undefined)];
      }

      case MIROpTag.MIRReturnAssign: {
        const opReturnAssign = op as MIRReturnAssign;
        return [this.MIRArgumentToTermExpr(opReturnAssign.name, fkey, this.MIRArgumentToTypeExpr(opReturnAssign.src, fkey)),
          this.MIRArgumentToTermExpr(opReturnAssign.src, fkey, undefined)];
      }




      // ---------------------------------------------------------------------------------------------------
      case MIROpTag.MIRAbort: { // IMPLEMENT:
        TranslatorBosqueFStar.debugging("MIRAbort Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
        return [new VarTerm("_MIRAbort", TranslatorBosqueFStar.int_type, fkey), new ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
        // Returns error
      }
      case MIROpTag.MIRDebug: { // IMPLEMENT:
        TranslatorBosqueFStar.debugging("MIRDDebug Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
        return [new VarTerm("_MIRDebug", TranslatorBosqueFStar.int_type, fkey), new ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
        // Print ignore
      }
      // ---------------------------------------------------------------------------------------------------



      case MIROpTag.MIRJump: {
        return [TranslatorBosqueFStar.skip_command, TranslatorBosqueFStar.skip_command];
      }

      case MIROpTag.MIRJumpCond: {
        return [TranslatorBosqueFStar.skip_command, TranslatorBosqueFStar.skip_command];
      }

      case MIROpTag.MIRJumpNone: {
        return [TranslatorBosqueFStar.skip_command, TranslatorBosqueFStar.skip_command];
      }
        
      case MIROpTag.MIRVarLifetimeStart: {
        return [TranslatorBosqueFStar.skip_command, TranslatorBosqueFStar.skip_command];
      }

      case MIROpTag.MIRVarLifetimeEnd: {
        return [TranslatorBosqueFStar.skip_command, TranslatorBosqueFStar.skip_command];
      }

      case MIROpTag.MIRPhi: { // DOUBLE CHECK
        const opPhi = op as MIRPhi;
        const currentType = this.checked_types.get(sanitizeName(fkey + opPhi.trgt.nameID));
        const typeFromSrc = this.MIRArgumentToTypeExpr(opPhi.src.get(comingFrom) as MIRRegisterArgument, fkey);
        if (currentType == undefined) {
          this.checked_types.set(sanitizeName(fkey + opPhi.trgt.nameID), typeFromSrc);
        }
        else {
          if (!currentType.equalTo(typeFromSrc)) {
            if (currentType instanceof UnionType) {
              if (typeFromSrc instanceof UnionType) {
                const previousElementsSet = new Set(Array.from(typeFromSrc.elements));
                currentType.elements.forEach(x => previousElementsSet.add(x));
                this.checked_types.set(sanitizeName(fkey + opPhi.trgt.nameID),
                  new UnionType(previousElementsSet));
              }
              else {
                currentType.elements.add(typeFromSrc);
                this.checked_types.set(sanitizeName(fkey + opPhi.trgt.nameID),
                  new UnionType(currentType.elements));
              }
            }
            else {
              if (typeFromSrc instanceof UnionType) {
                const previousElementsSet = new Set(Array.from(typeFromSrc.elements));
                previousElementsSet.add(currentType);
                this.checked_types.set(sanitizeName(fkey + opPhi.trgt.nameID),
                  new UnionType(previousElementsSet));
              }
              else {
                this.checked_types.set(sanitizeName(fkey + opPhi.trgt.nameID),
                  new UnionType(new Set<TypeExpr>([typeFromSrc, currentType])));
              }
            }
          }
        }
        return [this.MIRArgumentToTermExpr(opPhi.trgt, fkey, undefined),
          this.MIRArgumentToTermExpr(opPhi.src.get(comingFrom) as MIRRegisterArgument, fkey, undefined)];
      }

      case MIROpTag.MIRIsTypeOfNone: {
        const opIsTypeOfNone = op as MIRIsTypeOfNone;
        return [this.MIRArgumentToTermExpr(opIsTypeOfNone.trgt, fkey, TranslatorBosqueFStar.bool_type),
          new FuncTerm("isNoneBosque",
            [this.MIRArgumentToTermExpr(opIsTypeOfNone.arg, fkey, undefined)],
            TranslatorBosqueFStar.bool_type, fkey)];
      }

      case MIROpTag.MIRIsTypeOfSome: {
        const opIsTypeOfSome = op as MIRIsTypeOfSome;
        return [this.MIRArgumentToTermExpr(opIsTypeOfSome.trgt, fkey, TranslatorBosqueFStar.bool_type),
          new FuncTerm("isSomeBosque",
            [this.MIRArgumentToTermExpr(opIsTypeOfSome.arg, fkey, undefined)],
            TranslatorBosqueFStar.bool_type, fkey)];
      }



      // ---------------------------------------------------------------------------------------------------
      case MIROpTag.MIRIsTypeOf: { // IMPLEMENT:
        TranslatorBosqueFStar.debugging("MIRIsTypeOf Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
        return [new VarTerm("_MIRIsTypeOf", TranslatorBosqueFStar.int_type, fkey), new ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
      }
      case MIROpTag.MIRAccessConstantValue: {
        const opAccessConstantValue = op as MIRAccessConstantValue;

        return [this.MIRArgumentToTermExpr(opAccessConstantValue.trgt, fkey, this.MIRArgumentToTypeExpr(sanitizeName(opAccessConstantValue.ckey), "")), 
          this.MIRArgumentToTermExpr(opAccessConstantValue.ckey, "", undefined)
        ]; 
      }
      // ---------------------------------------------------------------------------------------------------

      default:
        //case MIROpTag.AccessConstField:
        //case MIROpTag.AccessCapturedVariable:
        //case MIROpTag.MIRAccessArgVariable:
        //case MIROpTag.MIRAccessLocalVariable:
        //case MIROpTag.ConstructorLambda:
        //case MIROpTag.CallStaticFunction: 
        //case MIROpTag.MIRInvokeKnownTarget: 
        //case MIROpTag.MIRCallLambda: 
        console.log(op);
        throw new Error("Operation " + op + " not defined");
    }
  }

  opsToExpr(ops: MIROp[], comingFrom: string, fkey: string, program: () => ExprExpr): ExprExpr {
    if (ops.length == 0) {
      return program();
    }
    else {
      const result = this.opToAssignment(ops[0], comingFrom, fkey);
      if (result[0] instanceof VarTerm) {
        const [lval, rval] = result as [VarTerm, TermExpr];
        if (lval.symbol_name == "_skip") {
          return this.opsToExpr(ops.slice(1), comingFrom, fkey, program);
        }
        else {
          return new AssignmentExpr(lval, rval, this.opsToExpr(ops.slice(1), comingFrom, fkey, program));
        }
      }
      else {
        return (result as [VarTerm, TermExpr][])
          .reduce((rest_expression, current_assignment) =>
            new AssignmentExpr(current_assignment[0], current_assignment[1], rest_expression),
            this.opsToExpr(ops.slice(1), comingFrom, fkey, program));
      }
    }
  }

  collectExpr(fkey: string) {
    const declarations = (this.invoke_declarations.get(fkey) as MIRInvokeBodyDecl);
    const map_blocks = (declarations.body as MIRBody).body;

    // ---------------------------------------------------------
    // Checking vtypes -----------------------------------------
    // const valueTypes = (declarations.body as MIRBody).vtypes;
    // console.log(`Inside ${fkey}`);
    // console.log(valueTypes);
    // console.log("\n");
    // ---------------------------------------------------------
    if (typeof (map_blocks) === "string") {
      throw new Error("The program with fkey " + fkey + " is just a string");
    }
    else {

      declarations.params.map(x =>
        this.checked_types.set(
          sanitizeName(fkey + x.name), 
          TranslatorBosqueFStar.stringVarToTypeExpr(x.type)
        )
      );

      const return_type = TranslatorBosqueFStar.stringVarToTypeExpr(declarations.resultType);
      const flow = computeBlockLinks(map_blocks);

      const traverse = (block: MIRBasicBlock, comingFrom: string): ExprExpr => {
        const current_flow = flow.get(block.label) as FlowLink;

        switch (current_flow.succs.size) {
          case 0: {
            const reg_name = sanitizeName("$$return");
            const continuation = () => new ReturnExpr(new VarTerm(reg_name, return_type, fkey));
            return this.opsToExpr(block.ops, comingFrom, fkey, continuation);
          }
          case 1: {
            const successor_label = current_flow.succs.values().next().value;
            const continuation = () => traverse(
              map_blocks.get(successor_label) as MIRBasicBlock, 
              block.label
            );
            return this.opsToExpr(block.ops.slice(0, -1), comingFrom, fkey, continuation);
          }
          case 2: {
            const jump_cond_op = block.ops[block.ops.length - 1] as MIRJumpCond;
            const reg_name = sanitizeName(jump_cond_op.arg.nameID);
            const condition = new VarTerm(reg_name, TranslatorBosqueFStar.bool_type, fkey);
            const true_branch = traverse(
              map_blocks.get(jump_cond_op.trueblock) as MIRBasicBlock, 
              block.label
            );
            const false_branch = traverse(
              map_blocks.get(jump_cond_op.falseblock) as MIRBasicBlock, 
              block.label
            );
            const continuation = () => new ConditionalExpr(condition, true_branch, false_branch);
            return this.opsToExpr(block.ops.slice(0, -1), comingFrom, fkey, continuation);
          }
          default: {
            throw new Error("Wrong Control-Flow graph. The out-degree of any node cannot be more than 2 in block: " + block);
          }
        }
      }
      if (!this.is_fkey_declared.has(fkey)) {
        this.is_fkey_declared.add(fkey);
        const entry_block = map_blocks.get("entry") as MIRBasicBlock;
        this.function_declarations.push(
          new FunctionDeclaration(declarations, traverse(entry_block, "entry"))
        );
      }
    }
  }

  generateFStarCode(fkey: string) {

    const user_defined_types_map: Map<string, MIRConceptTypeDecl | MIREntityTypeDecl>
      = new Map([...TranslatorBosqueFStar.concept_declarations, ...TranslatorBosqueFStar.entity_declarations]);
    const user_defined_types = this.extractProvidesRelation(user_defined_types_map);

    // --------------------------------------------------------------------------------------------------------------
    // BosqueTypes files
    printBosqueTypesFST(this.fstar_files_directory , user_defined_types);
    // --------------------------------------------------------------------------------------------------------------
    // ---------------------------------------------------------------------
    // BosqueTerms files
    printBosqueTermsFST(this.fstar_files_directory, user_defined_types_map);
    // ---------------------------------------------------------------------

    // The following stores the types of constant declarations
    // in checked_types
    this.constant_declarations.forEach(const_decl => {
      const body_decl = this.invoke_declarations.get(const_decl.value);
      if(body_decl instanceof MIRInvokeBodyDecl){
        const local_vtypes = body_decl.body.vtypes;
        if(local_vtypes instanceof Map){
          this.checked_types.set(
            sanitizeName(const_decl.cname), 
            TranslatorBosqueFStar.stringVarToTypeExpr(local_vtypes.get("$$return") as string)
          );
        }
      }
    })

    // The following stores the types of default declarations
    // in checked_types
    this.default_declarations.forEach(default_decl => {
      // This default_decl.value should always be not undefined
      // since we filter those @ line 99
      if(default_decl.value !== undefined){
        const body_decl = this.invoke_declarations.get(default_decl.value);
        if(body_decl instanceof MIRInvokeBodyDecl){
          const local_vtypes = body_decl.body.vtypes;
          local_vtypes;
          if(local_vtypes instanceof Map){
            this.checked_types.set(
              sanitizeName(default_decl.fname), 
              TranslatorBosqueFStar.stringVarToTypeExpr(local_vtypes.get("$$return") as string)
            );
          }
        }
      }
    })

    const fd = FS.openSync(this.fstar_files_directory + "/" + this.file_name, 'w');
    this.collectExpr(fkey);

    // --------------------------------------------------------------------------------------------------
    // Main file
    // -----------------------------------------------------------
    // Prelude
    FS.writeSync(fd, `module ${this.file_name.slice(0, -4)}\n\n`);
    FS.writeSync(fd, `open Sequence\n`);
    FS.writeSync(fd, `open List\n`);
    FS.writeSync(fd, `open BosqueTypes\n`);
    FS.writeSync(fd, `open BosqueTerms\n`);
    FS.writeSync(fd, `open BosqueCollections\n`);
    FS.writeSync(fd, `open Util\n`);
    FS.writeSync(fd, "\n");
    // -----------------------------------------------------------
    // ------------------------------------
    FS.writeSync(fd, "(* Type names *)\n");
    TypeExpr.declareTypeNames(fd);
    FS.writeSync(fd, "\n");
    // ------------------------------------
    // --------------------------------------------------------------------------------------------------
    // The following emits declaration of constant
    // in FStar
    FS.writeSync(fd, "(* Constant Declarations *)\n");
    this.constant_declarations.forEach(constant_decl => {
      // Constant declaration generally have only two blocks: entry and exit
      // We just `declare` the entry block
      const body_decl = this.invoke_declarations.get(constant_decl.value);
      if(body_decl instanceof MIRInvokeBodyDecl){
        body_decl.body.body.forEach(basic_block => {
          if (basic_block.label == "entry") {
            assert(basic_block.ops[0] instanceof MIRReturnAssign);
            const return_type = TranslatorBosqueFStar.stringVarToTypeExpr(constant_decl.declaredType);
            const continuation = () => new ReturnExpr(new VarTerm("___ir_ret__", return_type, fkey));
            this.checked_types.set(sanitizeName(constant_decl.cname), return_type);
            FS.writeSync(fd,
              `let ${sanitizeName(constant_decl.cname)} =\
                         \n${this.opsToExpr(basic_block.ops, "entry", "", continuation).toML(1, 0)}\n`);
          }
        });
      }
    });
    FS.writeSync(fd, "\n");
    // ---------------------------------------------------------------------------------------------------
    // The following emits declaration of default values
    // in FStar
    FS.writeSync(fd, "(* Default Declarations *)\n");
    this.default_declarations.forEach(default_decl => {
      // Constant declaration generally have only two blocks: entry and exit
      // We just `declare` the entry block
      if(default_decl.value !== undefined){
        const body_decl = this.invoke_declarations.get(default_decl.value);
        if(body_decl instanceof MIRInvokeBodyDecl){
          body_decl.body.body.forEach(basic_block => {
            if (basic_block.label == "entry") {
              assert(basic_block.ops[0] instanceof MIRReturnAssign);
              const return_type = TranslatorBosqueFStar.stringVarToTypeExpr(default_decl.declaredType);
              const continuation = () => new ReturnExpr(new VarTerm("___ir_ret__", return_type, fkey));
              this.checked_types.set(sanitizeName(default_decl.fname), return_type);
              FS.writeSync(fd,
                `let ${sanitizeName(default_decl.fname)} =\
                         \n${this.opsToExpr(basic_block.ops, "entry", "", continuation).toML(1, 0)}\n`);
            }
          });
        }
      }
    });
    FS.writeSync(fd, "\n");
    // --------------------------------------------------------------------------------------------------
    // -----------------------------------------------
    FS.writeSync(fd, "(* Function Declarations *)\n");
    this.function_declarations.map(x => x.print(fd));
    // -----------------------------------------------
    // --------------------------------------------------------------------------------------------------

    FS.closeSync(fd);

  }

  runFStarCode(z3rlimit : number, max_fuel : number, max_ifuel : number) { 
    const fstar_command = `fstar.exe ${this.file_name} --z3refresh --z3rlimit ${z3rlimit}\
    --max_fuel ${max_fuel} --max_ifuel ${max_ifuel} --include ${this.fstar_files_directory} --log_queries`;

    console.log(`Using the following command: ${fstar_command}`);
    ChildProcess.execSync(fstar_command);
    ChildProcess.execSync(`mv queries-${this.file_name.replace("fst", "smt2")} ${this.fstar_files_directory}`);
  }
}

class FunctionDeclaration {
  readonly declarations: MIRInvokeBodyDecl;
  readonly program: ExprExpr;

  constructor(declarations: MIRInvokeBodyDecl, program: ExprExpr) {
    this.declarations = declarations;
    this.program = program;
  }
  print(fd: number): void {
    const fkey = this.declarations.key;
    const args = this.declarations.params.map(x => x.name);
    const _type = new FuncType(
      this.declarations.params.map(x => TranslatorBosqueFStar.stringVarToTypeExpr(x.type)),
      TranslatorBosqueFStar.stringVarToTypeExpr(this.declarations.resultType));
    // TODO: Figure out how to include the following fields:
    // 1) recursive, 2) preconditions, 3) postconditions
    FS.writeSync(fd, `val ${sanitizeName(fkey)} : ${_type.valDeclare()}\n`);
    FS.writeSync(fd, `let ${sanitizeName(fkey)} ${args.join(" ")} = \n${this.program.toML(1, 1)}\n\n`);
  }
}

export { TranslatorBosqueFStar }
