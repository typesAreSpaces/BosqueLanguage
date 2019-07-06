// //-------------------------------------------------------------------------------------------------------
// // Copyright (C) Microsoft. All rights reserved.
// // Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
// //-------------------------------------------------------------------------------------------------------

// import { bosqueToIRBody, InfoFunctionCall } from "./util"
// import { MIRBasicBlock, MIROpTag, MIRBinCmp, MIRArgument, MIROp, MIRRegisterArgument, MIRVarLifetimeStart, MIRVarStore, MIRReturnAssign, MIRJumpCond, MIRBinOp, MIRPhi, MIRJump, MIRIsTypeOfSome, MIRIsTypeOfNone, MIRConstructorTuple, MIRConstructorLambda, MIRConstructorRecord, MIRAccessFromIndex, MIRAccessFromProperty, MIRCallNamespaceFunction } from "../compiler/mir_ops";
// import { topologicalOrder, computeBlockLinks, FlowLink } from "../compiler/mir_info";
// import { TypeExpr, IntType, BoolType, StringType, NoneType, UninterpretedType, FuncType, UnionType, AnyType, SomeType, TermType, TupleType, RecordType, LambdaType, RecordPropertyType } from "./type_expr";
// import { VarExpr, FuncExpr, TermExpr, ConstExpr } from "./term_expr";
// import { PredicateExpr, FormulaExpr, AndExpr, ImplExpr, NegExpr, makeConjunction, makeDisjuction, EqualityTerm } from "./formula_expr";

// let DEBUGGING = true;

// // TODO: Probably we dont need to instantiate
// // new elements from TypeExpr() ...

// // stringVariableToStringType : String[Variable] -> String[CoreType | Type]
// // Example : stringVariableToStringType = Map { x => 'NSCore::Int', y => 'NSCore::Bool', z => new_type, ... }
// let stringVariableToStringType: Map<string, string> = new Map<string, string>();

// // mapBlockCondition : String[Block] -> Set<FormulasExpr>
// let mapBlockCondition: Map<string, Set<FormulaExpr>> = new Map<string, Set<FormulaExpr>>();

// let BoxTrue = BoxFormulaExpr(new PredicateExpr("true", []));
// let BInt = new VarExpr("BInt", new UninterpretedType("BType"));
// let BBool = new VarExpr("BBool", new UninterpretedType("BType"));
// let BString = new VarExpr("BString", new UninterpretedType("BType"));
// let BAny = new VarExpr("BAny", new UninterpretedType("BType"));
// let BSome = new VarExpr("BSome", new UninterpretedType("BType"));
// let BNone = new VarExpr("BNone", new UninterpretedType("BType"));
// // let BTuple = new VarExpr("BTuple", new UninterpretedType("BType"));
// // let BRecord = new VarExpr("BRecord", new UninterpretedType("BRecord"));

// function debugging(x: any, flag: boolean) {
//     if (flag) {
//         console.log(x);
//     }
// }

// // resolveType : String[CoreType | Type] -> TypeExpr
// function resolveType(typeName: string): TypeExpr {
//     switch (typeName) {
//         case "NSCore::Int": {
//             return new IntType();
//         }
//         case "NSCore::Bool": {
//             return new BoolType();
//         }
//         // TODO: Fix this implementation
//         // NSCore::String are typed!
//         case "NSCore::String": {
//             return new StringType();
//         }
//         case "NSCore::None": {
//             return new NoneType();
//         }
//         case "NSCore::Any": {
//             return new AnyType();
//         }
//         case "NSCore::Some": {
//             return new SomeType();
//         }
//         default: {
//             if (typeName.includes("|")) {
//                 let collectionOfTypes = new Set<TypeExpr>(typeName.split(" | ").map(resolveType));
//                 if (collectionOfTypes.size === 1) {
//                     return Array.from(collectionOfTypes)[0];
//                 }
//                 else {
//                     return new UnionType(collectionOfTypes);
//                 }
//             }
//             if (typeName.includes("[")) {
//                 let collectionOfTypes = typeName.substr(1, typeName.length - 2).split(", ").map(resolveType);
//                 return new TupleType(collectionOfTypes);
//             }
//             if (typeName.includes("{")) {
//                 let collectionOfTypes = typeName.substr(1, typeName.length - 2).split(", ").map(pair => {
//                     let indexColon = pair.indexOf(":");
//                     let key = pair.substr(0, indexColon);
//                     let typeString = pair.substr(indexColon + 1);
//                     return ([key, resolveType(typeString)] as [string, TypeExpr]);
//                 });
//                 return new RecordType(collectionOfTypes);
//             } if (typeName.includes("(")) {
//                 let [args, resultString] = typeName.split(" -> ");
//                 let collectionOfTypesArgs = args.substr(1, args.length - 2).split(", ").map(pair => {
//                     let indexColon = pair.indexOf(":");
//                     let key = pair.substr(0, indexColon);
//                     let typeString = pair.substr(indexColon + 1);
//                     return ([key, resolveType(typeString)] as [string, TypeExpr]);
//                 });
//                 return new LambdaType(collectionOfTypesArgs, resolveType(resultString));
//             }
//             else {
//                 return new UninterpretedType(typeName);
//             }
//         }
//     }
// }

// // stringConstantToStringType : String[Constant] -> String[CoreType | Type]
// // I agree, this looks extremely dirty
// function stringConstantToStringType(value: string): string {
//     switch (value) {
//         case "true": {
//             return "NSCore::Bool";
//         }
//         case "false": {
//             return "NSCore::Bool";
//         }
//         case "none": {
//             return "NSCore::None"
//         }
//         default: {
//             if (value.length > 3) {
//                 switch (value.substr(1, 3)) {
//                     case "int": {
//                         return "NSCore::Int";
//                     }
//                     case "str": {
//                         return "NSCore::String";
//                     }
//                     default: {
//                         return "NSCore::Some";
//                     }
//                 }
//             }
//             else {
//                 return "NSCore::Some";
//             }
//         }
//     }
// }

// // Convention:
// // name <- src
// function conditionalAssignment(name: VarExpr, src: VarExpr, op: MIROp): FormulaExpr {
//     let srcName = src.symbolName;
//     let originalTypeSRC = stringVariableToStringType.get(srcName) as string;
//     let typeOfSRC = src.ty;
//     if (op instanceof MIRVarStore || op instanceof MIRReturnAssign) {
//         if (typeOfSRC instanceof UnionType) {
//             let assigments = Array.from((typeOfSRC as UnionType).elements).map(type => {
//                 switch (type.getType()) {
//                     case "Int": {
//                         stringVariableToStringType.set(srcName, "NSCore::Int");
//                         src.ty = new IntType();
//                         let result = new ImplExpr(
//                             new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"), [src]), BInt),
//                             new AndExpr(
//                                 new EqualityTerm(name, BoxTermExpr(UnboxTermExpr(src))),
//                                 new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"), [name]), BInt),
//                             )
//                         )
//                         stringVariableToStringType.set(srcName, originalTypeSRC);
//                         src.ty = typeOfSRC
//                         return result;
//                     }
//                     case "Bool": {
//                         stringVariableToStringType.set(srcName, "NSCore::Bool");
//                         src.ty = new BoolType();
//                         let result = new ImplExpr(
//                             new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"), [src]), BBool),
//                             new AndExpr(
//                                 new EqualityTerm(name, BoxTermExpr(UnboxTermExpr(src))),
//                                 new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"), [name]), BBool),
//                             )
//                         )
//                         stringVariableToStringType.set(srcName, originalTypeSRC);
//                         src.ty = typeOfSRC;
//                         return result;
//                     }
//                     case "String": {
//                         stringVariableToStringType.set(srcName, "NSCore::String");
//                         src.ty = new StringType();
//                         let result = new ImplExpr(
//                             new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"), [src]), BString),
//                             new AndExpr(
//                                 new EqualityTerm(name, BoxTermExpr(UnboxTermExpr(src))),
//                                 new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"), [name]), BString),
//                             )
//                         )
//                         stringVariableToStringType.set(srcName, originalTypeSRC);
//                         src.ty = typeOfSRC;
//                         return result;
//                     }
//                     case "None": {
//                         stringVariableToStringType.set(srcName, "NSCore::None");
//                         src.ty = new NoneType();
//                         let result = new ImplExpr(
//                             new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"), [src]), BNone),
//                             new AndExpr(
//                                 new EqualityTerm(name, BoxTermExpr(UnboxTermExpr(src))),
//                                 new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"), [name]), BNone),
//                             )
//                         )
//                         stringVariableToStringType.set(srcName, originalTypeSRC);
//                         src.ty = typeOfSRC;
//                         return result;
//                     }
//                     case "Any": {
//                         stringVariableToStringType.set(srcName, "NSCore::Any");
//                         src.ty = new AnyType();
//                         let result = new ImplExpr(
//                             new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"), [src]), BAny),
//                             new AndExpr(
//                                 new EqualityTerm(name, BoxTermExpr(UnboxTermExpr(src))),
//                                 new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"), [name]), BAny),
//                             )
//                         )
//                         stringVariableToStringType.set(srcName, originalTypeSRC);
//                         src.ty = typeOfSRC;
//                         return result;
//                     }
//                     case "Some": {
//                         stringVariableToStringType.set(srcName, "NSCore::Some");
//                         src.ty = new SomeType();
//                         let result = new ImplExpr(
//                             new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"), [src]), BSome),
//                             new AndExpr(
//                                 new EqualityTerm(name, BoxTermExpr(UnboxTermExpr(src))),
//                                 new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"), [name]), BSome),
//                             )
//                         )
//                         stringVariableToStringType.set(srcName, originalTypeSRC);
//                         src.ty = typeOfSRC;
//                         return result;
//                     }
//                     default: {
//                         throw new Error("The src wasn't a VarExpr");
//                     }
//                 }
//             });
//             return makeConjunction(assigments);
//         }
//         else {
//             return new EqualityTerm(name, BoxTermExpr(UnboxTermExpr(src)));
//         }
//     }
//     else {
//         throw new Error("Not an assignment operation");
//     }
// }

// function argumentToTermExpr(arg: MIRArgument, section: string): TermExpr {
//     // This branch handles variables
//     if (arg instanceof MIRRegisterArgument) {
//         let argName = section + "_" + arg.nameID;
//         return new VarExpr(argName, resolveType(stringVariableToStringType.get(argName) as string));
//     }
//     // This branch handles constants
//     else {
//         return new ConstExpr(arg.stringify(), resolveType(stringConstantToStringType(arg.nameID)));
//     }
// }

// // We currently only Unbox primitive types
// function UnboxTermExpr(x: TermExpr): TermExpr {
//     if (x instanceof ConstExpr) {
//         return x;
//     }
//     if (x instanceof VarExpr) {
//         let typeOfX = x.ty.getType();
//         switch (typeOfX) {
//             case "Int": {
//                 return new FuncExpr("UnboxInt", new IntType(), [x]);
//             }
//             case "Bool": {
//                 return new FuncExpr("UnboxBool", new BoolType(), [x]);
//             }
//             case "String": {
//                 return new FuncExpr("UnboxString", new StringType(), [x]);
//             }
//             case "None": {
//                 return new FuncExpr("UnboxNone", new NoneType(), [x]);
//             }
//             case "Any": {
//                 return new FuncExpr("UnboxAny", new AnyType(), [x]);
//             }
//             case "Some": {
//                 return new FuncExpr("UnboxSome", new SomeType(), [x]);
//             }
//         }
//     }
//     if (x instanceof FuncExpr) {
//         let typeOfImageOfX = (x.ty as FuncType).image.getType();
//         switch (typeOfImageOfX) {
//             case "Int": {
//                 return new FuncExpr("UnboxInt", new IntType(), [x]);
//             }
//             case "Bool": {
//                 return new FuncExpr("UnboxBool", new BoolType(), [x]);
//             }
//             case "String": {
//                 return new FuncExpr("UnboxString", new StringType(), [x]);
//             }
//             case "None": {
//                 return new FuncExpr("UnboxNone", new NoneType(), [x]);
//             }
//             case "Any": {
//                 return new FuncExpr("UnboxAny", new AnyType(), [x]);
//             }
//             case "Some": {
//                 return new FuncExpr("UnboxSome", new SomeType(), [x]);
//             }
//         }
//     }
//     // This branch handles constructors
//     if (!x.ty.isPrimitiveType) {
//         return x;
//     }
//     throw new Error(`Problem Unboxing ${x.sexpr()}`);
// }

// // We currently only Box primitive types
// function BoxTermExpr(x: TermExpr): TermExpr {
//     if (x instanceof VarExpr || x instanceof ConstExpr) {
//         switch (x.ty.getType()) {
//             case "Int": {
//                 return new FuncExpr("BoxInt", new TermType(), [x]);
//             }
//             case "Bool": {
//                 return new FuncExpr("BoxBool", new TermType(), [x]);
//             }
//             case "String": {
//                 return new FuncExpr("BoxString", new TermType(), [x]);
//             }
//             case "None": {
//                 return new FuncExpr("BoxNone", new TermType(), [x]);
//             }
//             case "Any": {
//                 return new FuncExpr("BoxAny", new TermType(), [x]);
//             }
//             case "Some": {
//                 return new FuncExpr("BoxSome", new TermType(), [x]);
//             }
//         }
//     }
//     if (x instanceof FuncExpr) {
//         let typeOfX = x.ty as FuncType;
//         switch (typeOfX.image.getType()) {
//             case "Int": {
//                 return new FuncExpr("BoxInt", new TermType(), [x]);
//             }
//             case "Bool": {
//                 return new FuncExpr("BoxBool", new TermType(), [x]);
//             }
//             case "String": {
//                 return new FuncExpr("BoxString", new TermType(), [x]);
//             }
//             case "None": {
//                 return new FuncExpr("BoxNone", new TermType(), [x]);
//             }
//             case "Any": {
//                 return new FuncExpr("BoxAny", new TermType(), [x]);
//             }
//             case "Some": {
//                 return new FuncExpr("BoxSome", new TermType(), [x]);
//             }
//         }
//     }
//     // This branch handles constructors
//     if (x.ty.isConstructor) {
//         return x;
//     }
//     throw new Error(`Problem Boxing this expression: ${x.sexpr()}`);
// }

// function UnboxFormulaExpr(x: FormulaExpr): FormulaExpr {
//     return new PredicateExpr("UnboxBool", [x]);
// }

// function BoxFormulaExpr(x: FormulaExpr): TermExpr {
//     return new FuncExpr("BoxBool", new TermType(), [x]);
// }

// function opToFormula(op: MIROp, info: InfoFunctionCall, nameBlock: string): FormulaExpr {
//     let section = info.section
//     let formula = new PredicateExpr("true", []) as FormulaExpr;
//     switch (op.tag) {
//         case MIROpTag.LoadConst:
//         case MIROpTag.LoadConstTypedString:
//         case MIROpTag.AccessNamespaceConstant:
//         case MIROpTag.AccessConstField:
//         case MIROpTag.LoadFieldDefaultValue: {
//             debugging("LoadFieldDefaultValue Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.AccessCapturedVariable: {
//             debugging("AcessCapturedVariable Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.AccessArgVariable: {
//             debugging("AccessArgVariable Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.AccessLocalVariable: {
//             debugging("AcessLocalVariable Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.ConstructorPrimary: {
//             debugging("ConstructorPrimary Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.ConstructorPrimaryCollectionEmpty: {
//             debugging("ConstructorPrimaryCollectionEmpty Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.ConstructorPrimaryCollectionSingletons: {
//             debugging("ConstructorPrimaryCollectionSingletons Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.ConstructorPrimaryCollectionCopies: {
//             debugging("ConstructorPrimaryCollectionCopies Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.ConstructorPrimaryCollectionMixed: {
//             debugging("ConstructorPrimaryCollectionMixed Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.ConstructorTuple: {
//             let opConstructorTuple = op as MIRConstructorTuple;

//             let regName = section + "_" + opConstructorTuple.trgt.nameID;
//             stringVariableToStringType.set(regName,
//                 "[" + opConstructorTuple.args.map(arg => {
//                     if (arg instanceof MIRRegisterArgument) {
//                         return stringVariableToStringType.get(section + "_" + arg.nameID);
//                     }
//                     else {
//                         return stringConstantToStringType(arg.nameID);
//                     }
//                 }).join(", ") + "]");

//             let regVar = argumentToTermExpr(opConstructorTuple.trgt, section);

//             formula = new EqualityTerm(new FuncExpr("TupleLength", new IntType(), [regVar]),
//                 new ConstExpr(opConstructorTuple.args.length.toString(), new IntType())
//             );

//             opConstructorTuple.args.map((arg, index) => {
//                 let argExpr = argumentToTermExpr(arg, section);
//                 formula = new AndExpr(formula,
//                     new EqualityTerm(
//                         new FuncExpr("TupleElement", argExpr.ty, [regVar, new ConstExpr(index.toString(), new IntType())]),
//                         BoxTermExpr(UnboxTermExpr(argExpr))))
//             });

//             return formula
//         }
//         case MIROpTag.ConstructorRecord: {
//             let opConstructorRecord = op as MIRConstructorRecord;

//             let regName = section + "_" + opConstructorRecord.trgt.nameID;
//             stringVariableToStringType.set(regName,
//                 "{" + opConstructorRecord.args.map(arg => {
//                     if (arg[1] instanceof MIRRegisterArgument) {
//                         return arg[0] + ":" + stringVariableToStringType.get(section + "_" + arg[1].nameID);
//                     }
//                     else {
//                         return arg[0] + ":" + stringConstantToStringType(arg[1].nameID);
//                     }
//                 }).join(", ") + "}");

//             let regVar = argumentToTermExpr(opConstructorRecord.trgt, section);

//             formula = new EqualityTerm(new FuncExpr("RecordLength", new IntType(), [regVar]),
//                 new ConstExpr(opConstructorRecord.args.length.toString(), new IntType())
//             );

//             opConstructorRecord.args.map((arg) => {
//                 let argExpr = argumentToTermExpr(arg[1], section);
//                 formula = new AndExpr(formula,
//                     new EqualityTerm(
//                         new FuncExpr("RecordElement", argExpr.ty, [regVar, new VarExpr(arg[0], new RecordPropertyType())]),
//                         BoxTermExpr(UnboxTermExpr(argExpr))))
//             });

//             return formula;
//         }
//         case MIROpTag.ConstructorLambda: {
//             debugging("ConstructorLambda Not implemented yet", DEBUGGING);
//             let opConstructorLambda = op as MIRConstructorLambda;
//             console.log(opConstructorLambda);
//             return formula;
//         }
//         case MIROpTag.CallNamespaceFunction: { // ------------------------------------------------------------------------------------------------------------
//             debugging("CallNamespaceFunction is being implemented", DEBUGGING);
//             let opCallNamespaceFunction = op as MIRCallNamespaceFunction;
//             console.log(opCallNamespaceFunction);

//             let [ir_body, sectionName] = bosqueToIRBody({directory: info.directory, fileName: info.fileName, section: opCallNamespaceFunction.fkey});
//             // Not sure about this
//             let formula = collectFormula(ir_body, {directory: info.directory, fileName: info.fileName, section: sectionName});
            

//             return formula;
//         }
//         case MIROpTag.CallStaticFunction: {
//             debugging("CallStaticFunction Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRAccessFromIndex: {
//             let opMIRAccessFromIndex = op as MIRAccessFromIndex;

//             let regName = section + "_" + opMIRAccessFromIndex.trgt.nameID;
//             let srcName = section + "_" + opMIRAccessFromIndex.arg.nameID;
//             let tupleTyString = stringVariableToStringType.get(srcName) as string;
//             let srcTypeString = tupleTyString.substr(1, tupleTyString.length - 2).split(", ")[opMIRAccessFromIndex.idx];

//             stringVariableToStringType.set(regName, srcTypeString);
//             let regVar = argumentToTermExpr(opMIRAccessFromIndex.trgt, section);
//             formula = new EqualityTerm(
//                 regVar,
//                 BoxTermExpr(UnboxTermExpr(
//                     new FuncExpr("TupleElement", resolveType(srcTypeString),
//                         [argumentToTermExpr(opMIRAccessFromIndex.arg, section),
//                         new ConstExpr(opMIRAccessFromIndex.idx.toString(), new IntType())]
//                     ))));

//             return formula;
//         }
//         case MIROpTag.MIRProjectFromIndecies: {
//             debugging("MIRProjectFromIndecies Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRAccessFromProperty: {
//             let opMIRAccessFromProperty = op as MIRAccessFromProperty;

//             let regName = section + "_" + opMIRAccessFromProperty.trgt.nameID;
//             let srcName = section + "_" + opMIRAccessFromProperty.arg.nameID;
//             let tupleTyString = stringVariableToStringType.get(srcName) as string;
//             let srcTypeAll = tupleTyString.substr(1, tupleTyString.length - 2).split(", ");

//             let srcTypeString: string = "";
//             for (let argString of srcTypeAll) {
//                 if (argString.startsWith(opMIRAccessFromProperty.property)) {
//                     srcTypeString = argString;
//                     break;
//                 }
//             }
//             srcTypeString = srcTypeString.slice(srcTypeString.indexOf(":") + 1);

//             stringVariableToStringType.set(regName, srcTypeString);
//             let regVar = argumentToTermExpr(opMIRAccessFromProperty.trgt, section);
//             formula = new EqualityTerm(
//                 regVar,
//                 BoxTermExpr(UnboxTermExpr(
//                     new FuncExpr("RecordElement", resolveType(srcTypeString),
//                         [argumentToTermExpr(opMIRAccessFromProperty.arg, section),
//                         new VarExpr(opMIRAccessFromProperty.property, new RecordPropertyType())]
//                     ))));

//             return formula;
//         }
//         case MIROpTag.MIRProjectFromProperties: {
//             debugging("MIRProjectFromProperties Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRAccessFromField: {
//             debugging("MIRAccessFromField Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRProjectFromFields: {
//             debugging("MIRProjectFromFields Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRProjectFromTypeTuple: {
//             debugging("MIRProjectFromTypeTuple Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRProjectFromTypeRecord: {
//             debugging("MIRProjectFromTypeRecord Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRProjectFromTypeConcept: {
//             debugging("MIRProjectFromTypeConcept Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRModifyWithIndecies: {
//             debugging("MIRModifyWithIndecies Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRModifyWithProperties: {
//             debugging("MIRModifyWithProperties Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRModifyWithFields: {
//             debugging("MIRModifyWithFields Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRStructuredExtendTuple: {
//             debugging("MIRStructuredExtendedTuple Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRStructuredExtendRecord: {
//             debugging("MIRStructuredExtendRecord Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRStructuredExtendObject: {
//             debugging("MIRStructuredExtendObject Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRInvokeKnownTarget: {
//             debugging("MIRInvokeKnownTarget Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRInvokeVirtualTarget: {
//             debugging("MIRInvokeVirtualTarget Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRCallLambda: {
//             debugging("MIRCallLambda Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRPrefixOp: {
//             debugging("MIRPrefixOp Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRBinOp: {
//             let opBinOp = op as MIRBinOp;
//             let regName = section + "_" + opBinOp.trgt.nameID;
//             // We follow the semantics given by
//             // the interpreter. Hence, the result of a 
//             // binary operation should be an Integer
//             stringVariableToStringType.set(regName, "NSCore::Int");
//             let rhsOfAssignmentTerm = new FuncExpr(opBinOp.op, new IntType(), [
//                 UnboxTermExpr(argumentToTermExpr(opBinOp.lhs, section)),
//                 UnboxTermExpr(argumentToTermExpr(opBinOp.rhs, section))
//             ]);
//             return new EqualityTerm(
//                 new VarExpr(regName, new IntType()),
//                 BoxTermExpr(rhsOfAssignmentTerm));
//         }
//         case MIROpTag.MIRBinEq: {
//             debugging("MIRBinEq Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRBinCmp: {
//             // The predicate returned is of type Bool
//             // because the operations to arrive at this
//             // point are <, <=, >, >= only
//             let opBinCmp = op as MIRBinCmp;

//             let regName = section + "_" + opBinCmp.trgt.nameID;
//             stringVariableToStringType.set(regName, "NSCore::Bool");

//             let lhsName = section + "_" + opBinCmp.lhs.nameID;
//             let rhsName = section + "_" + opBinCmp.rhs.nameID;
//             let originalTypeLHS = stringVariableToStringType.get(lhsName) as string;
//             let originalTypeRHS = stringVariableToStringType.get(rhsName) as string;

//             stringVariableToStringType.set(lhsName, "NSCore::Int");
//             stringVariableToStringType.set(rhsName, "NSCore::Int");
//             let opFormulaInt = new ImplExpr(
//                 new AndExpr(
//                     new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"), [argumentToTermExpr(opBinCmp.lhs, section)]), BInt),
//                     new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"), [argumentToTermExpr(opBinCmp.rhs, section)]), BInt)),
//                 new AndExpr(
//                     new EqualityTerm(
//                         new VarExpr(regName, new BoolType()),
//                         BoxFormulaExpr(new PredicateExpr(opBinCmp.op, [
//                             UnboxTermExpr(argumentToTermExpr(opBinCmp.lhs, section)),
//                             UnboxTermExpr(argumentToTermExpr(opBinCmp.rhs, section))
//                         ]))
//                     ),
//                     new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"), [argumentToTermExpr(opBinCmp.trgt, section)]), BBool)
//                 )
//             );

//             stringVariableToStringType.set(lhsName, "NSCore::String");
//             stringVariableToStringType.set(rhsName, "NSCore::String");
//             let opFormulaString = new ImplExpr(
//                 new AndExpr(
//                     new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"), [argumentToTermExpr(opBinCmp.lhs, section)]), BString),
//                     new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"), [argumentToTermExpr(opBinCmp.rhs, section)]), BString)),
//                 new AndExpr(
//                     new EqualityTerm(
//                         new VarExpr(regName, new BoolType()),
//                         BoxFormulaExpr(new PredicateExpr(opBinCmp.op + "_string", [
//                             UnboxTermExpr(argumentToTermExpr(opBinCmp.lhs, section)),
//                             UnboxTermExpr(argumentToTermExpr(opBinCmp.rhs, section))
//                         ]))
//                     ),
//                     new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"), [argumentToTermExpr(opBinCmp.trgt, section)]), BBool)
//                 )
//             );

//             stringVariableToStringType.set(lhsName, originalTypeLHS);
//             stringVariableToStringType.set(rhsName, originalTypeRHS);
//             return new AndExpr(opFormulaInt, opFormulaString);
//         }
//         case MIROpTag.MIRRegAssign: {
//             debugging("MIRRegAssign Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRTruthyConvert: {
//             debugging("MIRTruthyConvert Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRVarStore: {
//             let opVarStore = op as MIRVarStore;
//             let regName = section + "_" + opVarStore.name.nameID;
//             let srcName = opVarStore.src.nameID;
//             if (opVarStore.src instanceof MIRRegisterArgument) {
//                 stringVariableToStringType.set(regName, stringVariableToStringType.get(section + "_" + srcName) as string);
//             }
//             else {
//                 stringVariableToStringType.set(regName, stringConstantToStringType(srcName));
//             }
//             return conditionalAssignment(argumentToTermExpr(opVarStore.name, section), argumentToTermExpr(opVarStore.src, section), opVarStore);
//         }
//         case MIROpTag.MIRReturnAssign: {
//             let opReturnAssign = op as MIRReturnAssign;
//             let regName = section + "_" + opReturnAssign.name.nameID;
//             let srcName = opReturnAssign.src.nameID;
//             if (opReturnAssign.src instanceof MIRRegisterArgument) {
//                 stringVariableToStringType.set(regName, stringVariableToStringType.get(section + "_" + srcName) as string);
//             }
//             else {
//                 stringVariableToStringType.set(regName, stringConstantToStringType(srcName));
//             }
//             return conditionalAssignment(argumentToTermExpr(opReturnAssign.name, section), argumentToTermExpr(opReturnAssign.src, section), opReturnAssign);
//         }
//         case MIROpTag.MIRAbort: {
//             debugging("MIRAbort Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRDebug: {
//             debugging("MIRDDebug Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRJump: {
//             let opJump = op as MIRJump;
//             formula = UnboxFormulaExpr(new PredicateExpr("MIRJumpFormula", []));
//             let conditions = mapBlockCondition.get(nameBlock) as Set<FormulaExpr>;
//             if (conditions.size > 0) {
//                 for (let formula_ of conditions) {
//                     (mapBlockCondition.get(opJump.trgtblock) as Set<FormulaExpr>).add(formula_);
//                 }
//             }
//             return formula;
//         }
//         case MIROpTag.MIRJumpCond: {
//             let opJumpCond = op as MIRJumpCond;
//             formula = UnboxFormulaExpr(new PredicateExpr("MIRJumpCondFormula", []));
//             let regName = section + "_" + opJumpCond.arg.nameID;
//             let condition = new EqualityTerm(new PredicateExpr(regName, []), BoxTrue);
//             (mapBlockCondition.get(opJumpCond.trueblock) as Set<FormulaExpr>).add(condition);
//             (mapBlockCondition.get(opJumpCond.falseblock) as Set<FormulaExpr>).add(new NegExpr(condition));
//             return formula;
//         }
//         case MIROpTag.MIRJumpNone: {
//             debugging("MIRJumpNone Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRVarLifetimeStart: {
//             let opVarLifetimeStart = op as MIRVarLifetimeStart;
//             // We don't check if opVarLifetimeStart
//             // is an instance of MIRRegisterArgument
//             // because we know it is always a variable
//             let sectionName = section + "_" + opVarLifetimeStart.name;
//             stringVariableToStringType.set(sectionName, opVarLifetimeStart.rtype);
//             return formula;
//         }
//         case MIROpTag.MIRVarLifetimeEnd: {
//             debugging("MIRVarLifetimeEnd Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         case MIROpTag.MIRPhi: {
//             let opPhi = op as MIRPhi;
//             let targetName = section + "_" + opPhi.trgt.nameID;

//             let typePhi = new UnionType(new Set<TypeExpr>());
//             let typePhiString: Set<string> = new Set<string>();
//             let changeFormula = false;
//             opPhi.src.forEach((value, key) => {

//                 let valueExpr = argumentToTermExpr(value, section);
//                 stringVariableToStringType.set(targetName, stringVariableToStringType.get(valueExpr.symbolName) as string);
//                 typePhi.elements.add(valueExpr.ty);
//                 typePhiString.add(stringVariableToStringType.get(valueExpr.symbolName) as string);

//                 let consequence = new EqualityTerm(argumentToTermExpr(opPhi.trgt, section), valueExpr);

//                 let setOfConditions = mapBlockCondition.get(key) as Set<FormulaExpr>;
//                 if (!changeFormula) {
//                     changeFormula = true;
//                     if (setOfConditions.size === 0) {
//                         formula = consequence;
//                     }
//                     else {
//                         formula = new ImplExpr(makeDisjuction(setOfConditions), consequence);
//                     }
//                 }
//                 else {
//                     if (setOfConditions.size === 0) {
//                         formula = new AndExpr(formula, consequence);
//                     }
//                     else {
//                         formula = new AndExpr(formula, new ImplExpr(makeDisjuction(setOfConditions), consequence));
//                     }
//                 }
//             });

//             stringVariableToStringType.set(targetName, Array.from(typePhiString).join(" | "));
//             return formula;
//         }
//         case MIROpTag.MIRIsTypeOfNone: {
//             let opIsTypeOfNone = op as MIRIsTypeOfNone;

//             let regName = section + "_" + opIsTypeOfNone.trgt.nameID;
//             stringVariableToStringType.set(regName, "NSCore::Bool");

//             return new EqualityTerm(new VarExpr(regName, new BoolType()),
//                 BoxFormulaExpr(new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"),
//                     [argumentToTermExpr(opIsTypeOfNone.arg, section)]), BNone)));
//         }
//         case MIROpTag.MIRIsTypeOfSome: {
//             debugging("MIRIsTypeOfSome Not implemented yet", DEBUGGING);
//             let opIsTypeOfSome = op as MIRIsTypeOfSome;
//             console.log(opIsTypeOfSome);
//             return formula;
//         }
//         case MIROpTag.MIRIsTypeOf: {
//             debugging("MIRIsTypeOf Not implemented yet", DEBUGGING);
//             return formula;
//         }
//         default:
//             debugging("This might be a problem", DEBUGGING);
//             return formula;
//     }
// }

// // params is a sorted array of MIRFunctionParameter
// // i.e. the first element corresponds to the first argument, ... and so on.
// // We resolve nameing by prefixing the section variable to every name encountered
// function collectFormula(ibody: Map<string, MIRBasicBlock>, info: InfoFunctionCall): FormulaExpr {
//     const blocks = topologicalOrder(ibody);
//     const flow = computeBlockLinks(ibody);
//     let mapFormulas: Map<string, FormulaExpr> = new Map<string, FormulaExpr>();

//     // console.log("Blocks:-----------------------------------------------------------------------");
//     // console.log(blocks);
//     // console.log("More detailed Blocks:---------------------------------------------------------");
//     // blocks.map(x => console.log(x));
//     // console.log("More detailed++ Blocks:-------------------------------------------------------");
//     // blocks.map(x => console.log(x.jsonify()));

//     blocks.map(block => mapBlockCondition.set(block.label, new Set()));
//     blocks.map(block =>
//         mapFormulas.set(block.label,
//             makeConjunction(block.ops.map(op => opToFormula(op, info, block.label)))));

//     function traverse(block: MIRBasicBlock): FormulaExpr {
//         let currentFlow = flow.get(block.label) as FlowLink;
//         let currentBlockFormula = mapFormulas.get(block.label) as FormulaExpr;
//         switch (currentFlow.succs.size) {
//             case 0: {
//                 return currentBlockFormula;
//             }
//             case 1: {
//                 let successorLabel = currentFlow.succs.values().next().value;
//                 return new AndExpr(currentBlockFormula, traverse(ibody.get(successorLabel) as MIRBasicBlock));
//             }
//             case 2: {
//                 let jumpCondOp = block.ops[block.ops.length - 1] as MIRJumpCond;
//                 let regName = info.section + "_" + jumpCondOp.arg.nameID;
//                 let condition = new EqualityTerm(new PredicateExpr(regName, []), BoxTrue);
//                 let branchTrue = new ImplExpr(condition, traverse(ibody.get(jumpCondOp.trueblock) as MIRBasicBlock));
//                 let branchFalse = new ImplExpr(new NegExpr(condition), traverse(ibody.get(jumpCondOp.falseblock) as MIRBasicBlock));
//                 return new AndExpr(currentBlockFormula, new AndExpr(branchTrue, branchFalse));

//             }
//             default: {
//                 throw new Error("Wrong Control-Flow graph. The out-degree of any node cannot be more than 2.");
//             }
//         }
//     }
//     return traverse(ibody.get("entry") as MIRBasicBlock);
// }

// export { collectFormula, stringVariableToStringType, resolveType, UnboxTermExpr, BoxTermExpr, UnboxFormulaExpr, BoxFormulaExpr }