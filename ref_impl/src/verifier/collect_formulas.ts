//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRBasicBlock, MIROpTag, MIRBinCmp, MIRArgument, MIROp, MIRRegisterArgument, MIRVarLifetimeStart, MIRVarStore, MIRReturnAssign, MIRJumpCond, MIRBinOp, MIRPhi, MIRJump, MIRConstantArgument, MIRIsTypeOfSome, MIRIsTypeOfNone } from "../compiler/mir_ops";
import { topologicalOrder, computeBlockLinks, FlowLink } from "../compiler/mir_info";
import { TypeExpr, IntType, BoolType, StringType, NoneType, UninterpretedType, FuncType, UnionType, AnyType, SomeType, TermType } from "../verifier/type_expr";
import { VarExpr, FuncExpr, TermExpr } from "../verifier/term_expr";
import { PredicateExpr, FormulaExpr, AndExpr, EqualityExpr, ImplExpr, NegExpr, makeConjunction, makeDisjuction } from "../verifier/formula_expr";

let DEBUGGING = false;

// TODO: Probably we dont need to instantiate
// new elements from TypeExpr() ..

// Global variable to gather the types seen 
// in the program
// Keep in mind that blocks will be 
// process in a topological order
// Hence, it cannot be the case that
// we introduce inconsistency in the types
// of a well-typed program

// The following variables deserve to be explained:
// stringVariableToStringType : String[Variable] -> String[CoreType | Type]
// resolveType : String[CoreType | Type] -> TypeExpr
// stringConstantToStringType : String[Constant] -> String[CoreType | Type]
// Example : stringVariableToStringType = Map { x => 'NSCore::Int', y => 'NSCore::Bool', z => new_type, ... }
let stringVariableToStringType: Map<string, string> = new Map<string, string>();
// mapBlockCondition : String[Block] -> Set<FormulasExpr>
let mapBlockCondition: Map<string, Set<FormulaExpr>> = new Map<string, Set<FormulaExpr>>();
let BoxTrue = BoxFormulaExpr(new PredicateExpr("true", []));

function debugging(x: any, flag: boolean) {
    if (flag) {
        console.log(x);
    }
}
function resolveType(typeName: string): TypeExpr {
    switch (typeName) {
        case "NSCore::Int": {
            return new IntType();
        }
        case "NSCore::Bool": {
            return new BoolType();
        }
        // TODO: Fix this implementation
        // NSCore::String are typed!
        case "NSCore::String": {
            return new StringType();
        }
        case "NSCore::None": {
            return new NoneType();
        }
        case "NSCore::Any": {
            return new AnyType();
        }
        case "NSCore::Some": {
            return new SomeType();
        }
        default: {
            if (typeName.indexOf("|") > -1) {
                return new UnionType(new Set<TypeExpr>(typeName.split(" | ").map(resolveType)));
            }
            else {
                return new UninterpretedType(typeName);
            }
        }
    }
}
// I agree, this looks extremely dirty
function stringConstantToStringType(value: string): string {
    switch (value) {
        case "true": {
            return "NSCore::Bool";
        }
        case "false": {
            return "NSCore::Bool";
        }
        case "none": {
            return "NSCore::None"
        }
        default: {
            if (value.length > 3) {
                switch (value.substr(1, 3)) {
                    case "int": {
                        return "NSCore::Int";
                    }
                    case "str": {
                        return "NSCore::String";
                    }
                    default: {
                        return "NSCore::Some";
                    }
                }
            }
            else {
                return "NSCore::Some";
            }
        }
    }
}

function argumentToVarExpr(arg: MIRArgument, section: string): VarExpr {
    // This branch handles variables
    if (arg instanceof MIRRegisterArgument) {
        let argName = section + "_" + arg.nameID;
        return new VarExpr(argName, resolveType(stringVariableToStringType.get(argName) as string));
    }
    // This branch handles constants
    else {
        let argName = arg.stringify();
        let result = new VarExpr(argName, resolveType(stringConstantToStringType(arg.nameID)));
        return result;
    }
}

function UnboxTermExpr(x: TermExpr, isConstant: boolean): TermExpr {
    if (isConstant) {
        return x;
    }
    else {
        if (x instanceof VarExpr) {
            switch (x.ty.getType()) {
                case "Int": {
                    return new FuncExpr("UnboxInt", new IntType(), [x]);
                }
                case "Bool": {
                    return new FuncExpr("UnboxBool", new BoolType(), [x]);
                }
                case "String": {
                    return new FuncExpr("UnboxString", new StringType(), [x]);
                }
                case "None": {
                    return new FuncExpr("UnboxNone", new NoneType(), [x]);
                }
                case "Any": {
                    return new FuncExpr("UnboxAny", new AnyType(), [x]);
                }
                case "Some": {
                    return new FuncExpr("UnboxSome", new SomeType(), [x]);
                }
            }
        }
        if (x instanceof FuncExpr) {
            let typeOfX = x.ty as FuncType;
            switch (typeOfX.image.getType()) {
                case "Int": {
                    return new FuncExpr("UnboxInt", new IntType(), [x]);
                }
                case "Bool": {
                    return new FuncExpr("UnboxBool", new BoolType(), [x]);
                }
                case "String": {
                    return new FuncExpr("UnboxString", new StringType(), [x]);
                }
                case "None": {
                    return new FuncExpr("UnboxNone", new NoneType(), [x]);
                }
                case "Any": {
                    return new FuncExpr("UnboxAny", new AnyType(), [x]);
                }
                case "Some": {
                    return new FuncExpr("UnboxSome", new SomeType(), [x]);
                }
            }
        }
        console.log(x);
        throw new Error(`Problem Unboxing ${x.sexpr()}`);
    }
}

function BoxTermExpr(x: TermExpr): TermExpr {
    if (x instanceof VarExpr) {
        switch (x.ty.getType()) {
            case "Int": {
                return new FuncExpr("BoxInt", new TermType(), [x]);
            }
            case "Bool": {
                return new FuncExpr("BoxBool", new TermType(), [x]);
            }
            case "String": {
                return new FuncExpr("BoxString", new TermType(), [x]);
            }
            case "None": {
                return new FuncExpr("BoxNone", new TermType(), [x]);
            }
            case "Any": {
                return new FuncExpr("BoxAny", new TermType(), [x]);
            }
            case "Some": {
                return new FuncExpr("BoxSome", new TermType(), [x]);
            }
        }
    }
    if (x instanceof FuncExpr) {
        let typeOfX = x.ty as FuncType;
        switch (typeOfX.image.getType()) {
            case "Int": {
                return new FuncExpr("BoxInt", new TermType(), [x]);
            }
            case "Bool": {
                return new FuncExpr("BoxBool", new TermType(), [x]);
            }
            case "String": {
                return new FuncExpr("BoxString", new TermType(), [x]);
            }
            case "None": {
                return new FuncExpr("BoxNone", new TermType(), [x]);
            }
            case "Any": {
                return new FuncExpr("BoxAny", new TermType(), [x]);
            }
            case "Some": {
                return new FuncExpr("BoxSome", new TermType(), [x]);
            }
        }
    }
    throw new Error(`Problem Boxing this expression: ${x.sexpr()}`);

}

function UnboxFormulaExpr(x: FormulaExpr): FormulaExpr {
    return new PredicateExpr("UnboxBool", [x]);
}

function BoxFormulaExpr(x: FormulaExpr): TermExpr {
    return new FuncExpr("BoxBool", new FuncType([x.ty], new TermType()), [x]);
}

function opToFormula(op: MIROp, section: string, nameBlock: string): FormulaExpr {
    let formula = new PredicateExpr("true", []) as FormulaExpr;
    switch (op.tag) {
        case MIROpTag.LoadConst:
        case MIROpTag.LoadConstTypedString:
        case MIROpTag.AccessNamespaceConstant:
        case MIROpTag.AccessConstField:
        case MIROpTag.LoadFieldDefaultValue: {
            debugging("LoadFieldDefaultValue Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.AccessCapturedVariable: {
            debugging("AcessCapturedVariable Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.AccessArgVariable: {
            debugging("AccessArgVariable Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.AccessLocalVariable: {
            debugging("AcessLocalVariable Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.ConstructorPrimary: {
            debugging("ConstructorPrimary Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.ConstructorPrimaryCollectionEmpty: {
            debugging("ConstructorPrimaryCollectionEmpty Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.ConstructorPrimaryCollectionSingletons: {
            debugging("ConstructorPrimaryCollectionSingletons Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.ConstructorPrimaryCollectionCopies: {
            debugging("ConstructorPrimaryCollectionCopies Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.ConstructorPrimaryCollectionMixed: {
            debugging("ConstructorPrimaryCollectionMixed Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.ConstructorTuple: {
            debugging("ConstructorTuple Not implemented yet", DEBUGGING);
            return formula
        }
        case MIROpTag.ConstructorRecord: {
            debugging("ConstructorRecord Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.ConstructorLambda: {
            debugging("ConstructorLambda Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.CallNamespaceFunction: {
            debugging("CallNamespaceFunction Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.CallStaticFunction: {
            debugging("CallStaticFunction Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRAccessFromIndex: {
            debugging("MIRAccessFromIndex Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRProjectFromIndecies: {
            debugging("MIRProjectFromIndecies Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRAccessFromProperty: {
            debugging("MIRAcessFromProperty Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRProjectFromProperties: {
            debugging("MIRProjectFromProperties Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRAccessFromField: {
            debugging("MIRAccessFromField Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRProjectFromFields: {
            debugging("MIRProjectFromFields Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRProjectFromTypeTuple: {
            debugging("MIRProjectFromTypeTuple Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRProjectFromTypeRecord: {
            debugging("MIRProjectFromTypeRecord Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRProjectFromTypeConcept: {
            debugging("MIRProjectFromTypeConcept Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRModifyWithIndecies: {
            debugging("MIRModifyWithIndecies Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRModifyWithProperties: {
            debugging("MIRModifyWithProperties Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRModifyWithFields: {
            debugging("MIRModifyWithFields Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRStructuredExtendTuple: {
            debugging("MIRStructuredExtendedTuple Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRStructuredExtendRecord: {
            debugging("MIRStructuredExtendRecord Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRStructuredExtendObject: {
            debugging("MIRStructuredExtendObject Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRInvokeKnownTarget: {
            debugging("MIRInvokeKnownTarget Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRInvokeVirtualTarget: {
            debugging("MIRInvokeVirtualTarget Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRCallLambda: {
            debugging("MIRCallLambda Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRPrefixOp: {
            debugging("MIRPrefixOp Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRBinOp: {
            let opBinOp = op as MIRBinOp;
            let regName = section + "_" + opBinOp.trgt.nameID;
            // We assume the expressions are well-typed.
            // So we assign the type of the register
            // the type of the lhs element in the operation
            let stringTypeOfRHS = stringVariableToStringType.get(section + "_" + opBinOp.lhs.nameID) as string;
            stringVariableToStringType.set(regName, stringTypeOfRHS);
            let typeOfRHS = resolveType(stringTypeOfRHS);
            let rhsOfAssignmentTerm = new FuncExpr(opBinOp.op, new FuncType([typeOfRHS, typeOfRHS], typeOfRHS), [
                UnboxTermExpr(argumentToVarExpr(opBinOp.lhs, section), opBinOp.lhs instanceof MIRConstantArgument),
                UnboxTermExpr(argumentToVarExpr(opBinOp.rhs, section), opBinOp.rhs instanceof MIRConstantArgument)
            ]);
            let opFormula = new EqualityExpr(
                new VarExpr(regName, typeOfRHS),
                BoxTermExpr(rhsOfAssignmentTerm));
            return opFormula;
        }
        case MIROpTag.MIRBinEq: {
            debugging("MIRBinEq Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRBinCmp: {
            // The predicate returned is of type Bool
            // because the operations to arrive at this
            // point are <, <=, >, >= only
            let opBinCmp = op as MIRBinCmp;
            let opFormula = new PredicateExpr(opBinCmp.op, [
                UnboxTermExpr(argumentToVarExpr(opBinCmp.lhs, section), opBinCmp.lhs instanceof MIRConstantArgument),
                UnboxTermExpr(argumentToVarExpr(opBinCmp.rhs, section), opBinCmp.rhs instanceof MIRConstantArgument)
            ]);
            let regName = section + "_" + opBinCmp.trgt.nameID;
            stringVariableToStringType.set(regName, "NSCore::Bool");
            // TODO: Needs testing
            return new EqualityExpr(new VarExpr(regName, new BoolType()), BoxFormulaExpr(opFormula));
        }
        case MIROpTag.MIRRegAssign: {
            debugging("MIRRegAssign Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRTruthyConvert: {
            debugging("MIRTruthyConvert Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRVarStore: {
            let opVarStore = op as MIRVarStore;
            let regName = section + "_" + opVarStore.name.nameID;
            let srcName = opVarStore.src.nameID;
            if (opVarStore.src instanceof MIRRegisterArgument) {
                stringVariableToStringType.set(regName, stringVariableToStringType.get(section + "_" + srcName) as string);
            }
            else {
                stringVariableToStringType.set(regName, stringConstantToStringType(srcName));
            }
            let opFormula = new EqualityExpr(
                argumentToVarExpr(opVarStore.name, section),
                BoxTermExpr(UnboxTermExpr(argumentToVarExpr(opVarStore.src, section), opVarStore.src instanceof MIRConstantArgument)));
            return opFormula;
        }
        case MIROpTag.MIRReturnAssign: {
            let opReturnAssign = op as MIRReturnAssign;
            console.log(opReturnAssign);
            let regName = section + "_" + opReturnAssign.name.nameID;
            let srcName = opReturnAssign.src.nameID;
            if (opReturnAssign.src instanceof MIRRegisterArgument) {
                stringVariableToStringType.set(regName, stringVariableToStringType.get(section + "_" + srcName) as string);
            }
            else {
                stringVariableToStringType.set(regName, stringConstantToStringType(srcName));
            }
            let opFormula = new EqualityExpr(
                argumentToVarExpr(opReturnAssign.name, section),
                BoxTermExpr(UnboxTermExpr(argumentToVarExpr(opReturnAssign.src, section), opReturnAssign.src instanceof MIRConstantArgument)));
            return opFormula;
        }
        case MIROpTag.MIRAbort: {
            debugging("MIRAbort Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRDebug: {
            debugging("MIRDDebug Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRJump: {
            let opJump = op as MIRJump;
            formula = UnboxFormulaExpr(new PredicateExpr("MIRJumpFormula", []));
            let conditions = mapBlockCondition.get(nameBlock) as Set<FormulaExpr>;
            if (conditions.size > 0) {
                for (let formula_ of conditions) {
                    (mapBlockCondition.get(opJump.trgtblock) as Set<FormulaExpr>).add(formula_);
                }
            }
            return formula;
        }
        case MIROpTag.MIRJumpCond: {
            let opJumpCond = op as MIRJumpCond;
            formula = UnboxFormulaExpr(new PredicateExpr("MIRJumpCondFormula", []));
            let regName = section + "_" + opJumpCond.arg.nameID;
            let condition = new EqualityExpr(new PredicateExpr(regName, []), BoxTrue);
            (mapBlockCondition.get(opJumpCond.trueblock) as Set<FormulaExpr>).add(condition);
            (mapBlockCondition.get(opJumpCond.falseblock) as Set<FormulaExpr>).add(new NegExpr(condition));
            return formula;
        }
        case MIROpTag.MIRJumpNone: {
            debugging("MIRJumpNone Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRVarLifetimeStart: {
            let opVarLifetimeStart = op as MIRVarLifetimeStart;
            // We don't check if opVarLifetimeStart
            // is an instance of MIRRegisterArgument
            // because we know it is always a variable
            let sectionName = section + "_" + opVarLifetimeStart.name;
            stringVariableToStringType.set(sectionName, opVarLifetimeStart.rtype);
            // TODO: Here is where we include the type relation
            // of variables
            return formula;
        }
        case MIROpTag.MIRVarLifetimeEnd: {
            debugging("MIRVarLifetimeEnd Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRPhi: {
            let opPhi = op as MIRPhi;
            let targetName = section + "_" + opPhi.trgt.nameID;

            // TODO: Fix this using UnionType or a
            // clever approach. Currently is just set to 
            // be the IntType for the purpose of the 
            // max function demo
            stringVariableToStringType.set(targetName, "NSCore::Int");

            let changeFormula = false;
            opPhi.src.forEach((value, key) => {
                let consequence = new EqualityExpr(argumentToVarExpr(opPhi.trgt, section), argumentToVarExpr(value, section));
                let setOfConditions = mapBlockCondition.get(key) as Set<FormulaExpr>;
                if (!changeFormula) {
                    changeFormula = true;
                    if (setOfConditions.size === 0) {
                        formula = consequence;
                    }
                    else {
                        formula = new ImplExpr(makeDisjuction(setOfConditions), consequence);
                    }
                }
                else {
                    if (setOfConditions.size === 0) {
                        formula = new AndExpr(formula, consequence);
                    }
                    else {
                        formula = new AndExpr(formula, new ImplExpr(makeDisjuction(setOfConditions), consequence));
                    }
                }
            });
            return formula;
        }
        case MIROpTag.MIRIsTypeOfNone: {
            debugging("MIRIsTypeOfNone Not implemented yet", DEBUGGING);
            let opIsTypeOfNone = op as MIRIsTypeOfNone;
            console.log(opIsTypeOfNone)
            return formula;
        }
        case MIROpTag.MIRIsTypeOfSome: {
            debugging("MIRIsTypeOfSome Not implemented yet", DEBUGGING);
            let opIsTypeOfSome = op as MIRIsTypeOfSome;
            console.log(opIsTypeOfSome);
            return formula;
        }
        case MIROpTag.MIRIsTypeOf: {
            debugging("MIRIsTypeOf Not implemented yet", DEBUGGING);
            return formula;
        }
        default:
            debugging("This might be a problem", DEBUGGING);
            return formula;
    }
}

// params is a sorted array of MIRFunctionParameter
// i.e. the first element corresponds to the first argument, ... and so on.
// Resolve names by prefixing section to every name encountered
function collectFormulas(ibody: Map<string, MIRBasicBlock>, section: string): FormulaExpr {
    const blocks = topologicalOrder(ibody);
    const flow = computeBlockLinks(ibody);
    let mapFormulas: Map<string, FormulaExpr> = new Map<string, FormulaExpr>();

    // console.log("Blocks:-----------------------------------------------------------------------");
    // console.log(blocks);
    // console.log("More detailed Blocks:---------------------------------------------------------");
    // blocks.map(x => console.log(x));
    // console.log("More detailed++ Blocks:-------------------------------------------------------");
    // blocks.map(x => console.log(x.jsonify()));

    blocks.map(block => mapBlockCondition.set(block.label, new Set()));
    blocks.map(block =>
        mapFormulas.set(block.label,
            makeConjunction(block.ops.map(op => opToFormula(op, section, block.label)))));

    function traverse(block: MIRBasicBlock): FormulaExpr {
        let currentFlow = flow.get(block.label) as FlowLink;
        let currentBlockFormula = mapFormulas.get(block.label) as FormulaExpr;
        switch (currentFlow.succs.size) {
            case 0: {
                return currentBlockFormula;
            }
            case 1: {
                let successorLabel = currentFlow.succs.values().next().value;
                return new AndExpr(currentBlockFormula, traverse(ibody.get(successorLabel) as MIRBasicBlock));
            }
            case 2: {
                let jumpCondOp = block.ops[block.ops.length - 1] as MIRJumpCond;
                let regName = section + "_" + jumpCondOp.arg.nameID;
                // let condition = UnboxFormulaExpr(new PredicateExpr(regName, []));
                let condition = new EqualityExpr(new PredicateExpr(regName, []), BoxTrue);
                let branchTrue = new ImplExpr(condition, traverse(ibody.get(jumpCondOp.trueblock) as MIRBasicBlock));
                let branchFalse = new ImplExpr(new NegExpr(condition), traverse(ibody.get(jumpCondOp.falseblock) as MIRBasicBlock));
                return new AndExpr(currentBlockFormula, new AndExpr(branchTrue, branchFalse));

            }
            default: {
                throw new Error("Wrong Control-Flow graph. The out-degree of any node cannot be more than 2.");
            }
        }
    }
    return traverse(ibody.get("entry") as MIRBasicBlock);
}

export { collectFormulas, stringVariableToStringType, UnboxTermExpr, BoxTermExpr, UnboxFormulaExpr, BoxFormulaExpr }