//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRBasicBlock, MIROpTag, MIRBinCmp, MIRArgument, MIROp, MIRRegisterArgument, MIRVarLifetimeStart, MIRVarStore, MIRReturnAssign, MIRJump, MIRJumpCond, MIRBinOp, MIRPhi } from "../compiler/mir_ops";
import { topologicalOrder, computeBlockLinks, FlowLink } from "../compiler/mir_info";
import { TypeExpr, IntType, BoolType, StringType, UninterpretedType } from "../verifier/type_expr";
import { VarExpr, FuncExpr } from "../verifier/term_expr";
import { PredicateExpr, FormulaExpr, AndExpr, EqualityExpr, ImplExpr, NegExpr } from "../verifier/formula_expr";

// TODO: Probably we dont need to instantiate
// new elements from TypeExpr() ..

// Global variable to gather the types seen 
// in the program
// Keep in mind that blocks will be 
// process in a topological order
// Hence, it cannot be the case that
// we introduce inconsistency in the types
// of a well-typed program
let typesSeen: Map<string, string> = new Map<string, string>();

// I agree, this looks extremely dirty
function resolveType(typeName: string): TypeExpr {
    switch (typeName) {
        case "NSCore::Int": {
            return new IntType();
        }
        case "NSCore::Bool": {
            return new BoolType();
        }
        case "NSCore::String": {
            return new StringType();
        }
        case "true": {
            return new BoolType();
        }
        case "false": {
            return new BoolType();
        }
        default: {
            if (typeName.length > 3) {
                switch (typeName.substr(0, 4)) {
                    case "=int": {
                        return new IntType();
                    }
                    case "=str": {
                        return new StringType();
                    }
                    default: {
                        return new UninterpretedType(typeName);
                    }
                }
            }
            else {
                return new UninterpretedType(typeName);
            }
        }
    }
}

function argumentToVarExpr(arg: MIRArgument, section: string): VarExpr {
    if (arg instanceof MIRRegisterArgument) {
        let argName = section + "__" + arg.nameID;
        return new VarExpr(argName, resolveType(typesSeen.get(argName) as string));
    }
    else {
        let argName = arg.stringify();
        let result = new VarExpr(argName, resolveType(arg.nameID));
        // With this we prevent printing constant argument
        // as declarations in Z3
        VarExpr.symbolTable.set(argName, true);
        return result;
    }
}

function opToFormula(op: MIROp, section: string): FormulaExpr {
    let formula = new PredicateExpr("ahhh", []);
    switch (op.tag) {
        case MIROpTag.LoadConst:
        case MIROpTag.LoadConstTypedString:
        case MIROpTag.AccessNamespaceConstant:
        case MIROpTag.AccessConstField:
        case MIROpTag.LoadFieldDefaultValue: {
            console.log("LoadFieldDefaultValue Not implemented yet");
            return formula;
        }
        case MIROpTag.AccessCapturedVariable: {
            console.log("AcessCapturedVariable Not implemented yet");
            return formula;
        }
        case MIROpTag.AccessArgVariable: {
            console.log("AccessArgVariable Not implemented yet");
            return formula;
        }
        case MIROpTag.AccessLocalVariable: {
            console.log("AcessLocalVariable Not implemented yet");
            return formula;
        }
        case MIROpTag.ConstructorPrimary: {
            console.log("ConstructorPrimary Not implemented yet");
            return formula;
        }
        case MIROpTag.ConstructorPrimaryCollectionEmpty: {
            console.log("ConstructorPrimaryCollectionEmpty Not implemented yet");
            return formula;
        }
        case MIROpTag.ConstructorPrimaryCollectionSingletons: {
            console.log("ConstructorPrimaryCollectionSingletons Not implemented yet");
            return formula;
        }
        case MIROpTag.ConstructorPrimaryCollectionCopies: {
            console.log("ConstructorPrimaryCollectionCopies Not implemented yet");
            return formula;
        }
        case MIROpTag.ConstructorPrimaryCollectionMixed: {
            console.log("ConstructorPrimaryCollectionMixed Not implemented yet");
            return formula;
        }
        case MIROpTag.ConstructorTuple: {
            console.log("ConstructorTuple Not implemented yet");
            return formula
        }
        case MIROpTag.ConstructorRecord: {
            console.log("ConstructorRecord Not implemented yet");
            return formula;
        }
        case MIROpTag.ConstructorLambda: {
            console.log("ConstructorLambda Not implemented yet");
            return formula;
        }
        case MIROpTag.CallNamespaceFunction: {
            console.log("CallNamespaceFunction Not implemented yet");
            return formula;
        }
        case MIROpTag.CallStaticFunction: {
            console.log("CallStaticFunction Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRAccessFromIndex: {
            console.log("MIRAccessFromIndex Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRProjectFromIndecies: {
            console.log("MIRProjectFromIndecies Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRAccessFromProperty: {
            console.log("MIRAcessFromProperty Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRProjectFromProperties: {
            console.log("MIRProjectFromProperties Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRAccessFromField: {
            console.log("MIRAccessFromField Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRProjectFromFields: {
            console.log("MIRProjectFromFields Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRProjectFromTypeTuple: {
            console.log("MIRProjectFromTypeTuple Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRProjectFromTypeRecord: {
            console.log("MIRProjectFromTypeRecord Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRProjectFromTypeConcept: {
            console.log("MIRProjectFromTypeConcept Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRModifyWithIndecies: {
            console.log("MIRModifyWithIndecies Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRModifyWithProperties: {
            console.log("MIRModifyWithProperties Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRModifyWithFields: {
            console.log("MIRModifyWithFields Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRStructuredExtendTuple: {
            console.log("MIRStructuredExtendedTuple Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRStructuredExtendRecord: {
            console.log("MIRStructuredExtendRecord Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRStructuredExtendObject: {
            console.log("MIRStructuredExtendObject Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRInvokeKnownTarget: {
            console.log("MIRInvokeKnownTarget Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRInvokeVirtualTarget: {
            console.log("MIRInvokeVirtualTarget Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRCallLambda: {
            console.log("MIRCallLambda Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRPrefixOp: {
            console.log("MIRPrefixOp Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRBinOp: {
            let opBinOp = op as MIRBinOp;
            let regName = opBinOp.trgt.nameID[0] == "#" ? "__" + opBinOp.trgt.nameID.slice(1) : opBinOp.trgt.nameID;
            // We assume the expressions are well-typed.
            // So we assign the type of the register
            // the type of the lhs element in the operation
            let typeOfrhsTerm = resolveType(typesSeen.get(section + "__" + opBinOp.lhs.nameID) as string);
            let rhsOfAssignmentTerm = new FuncExpr(opBinOp.op, typeOfrhsTerm, [
                argumentToVarExpr(opBinOp.lhs, section),
                argumentToVarExpr(opBinOp.rhs, section)
            ]);
            let opFormula = new EqualityExpr(new VarExpr(regName, typeOfrhsTerm), rhsOfAssignmentTerm);
            return opFormula;
        }
        case MIROpTag.MIRBinEq: {
            console.log("MIRBinEq Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRBinCmp: {
            // The predicate returned is of type Bool
            // because the operations to arrive at this
            // point are <, <=, >, >= only
            let opBinCmp = op as MIRBinCmp;
            let opFormula = new PredicateExpr(opBinCmp.op, [
                argumentToVarExpr(opBinCmp.lhs, section),
                argumentToVarExpr(opBinCmp.rhs, section)
            ]);

            let regName = opBinCmp.trgt.nameID[0] == "#" ? "__" + opBinCmp.trgt.nameID.slice(1) : opBinCmp.trgt.nameID;
            let regFormula = new EqualityExpr(new PredicateExpr(regName, []), opFormula);
            return new AndExpr(opFormula, regFormula);
        }
        case MIROpTag.MIRRegAssign: {
            console.log("MIRRegAssign Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRTruthyConvert: {
            console.log("MIRTruthyConvert Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRVarStore: {
            let opVarStore = op as MIRVarStore;
            // console.log("Implementing MIRVarStore--------------------------------------");
            // console.log(opVarStore);
            // TODO: Currently, the commented code, 
            // which is the right implementation,
            // doesn't work as expected due to 
            // some issues with the global 
            // variable typesSeen
            let regName = section + "__" + opVarStore.name.nameID;
            let srcName = section + "__" + opVarStore.src.nameID;
            typesSeen.set(regName, typesSeen.get(srcName) as string);
            let opFormula = new EqualityExpr(
                argumentToVarExpr(opVarStore.src, section),
                argumentToVarExpr(opVarStore.name, section));
            return opFormula;
        }
        case MIROpTag.MIRReturnAssign: {
            let opReturnAssign = op as MIRReturnAssign;
            // console.log("Implementing MIRReturnAssign--------------------------------------");
            // console.log(opReturnAssign);
            let regName = section + "__" + opReturnAssign.name.nameID;
            let srcName = section + "__" + opReturnAssign.src.nameID;
            // The register Variable will have the same
            // type of the src Variable
            typesSeen.set(regName, typesSeen.get(srcName) as string);
            let opFormula = new EqualityExpr(
                argumentToVarExpr(opReturnAssign.name, section),
                argumentToVarExpr(opReturnAssign.src, section));
            return opFormula;
        }
        case MIROpTag.MIRAbort: {
            console.log("MIRAbort Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRDebug: {
            console.log("MIRDDebug Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRJump: {
            let opJump = op as MIRJump;
            opJump;
            // console.log("Implementing MIRJump--------------------------------------------------");
            // console.log(opJump);
            return formula;
        }
        case MIROpTag.MIRJumpCond: {
            let opJumpCond = op as MIRJumpCond;
            opJumpCond;
            // console.log("Implementing MIRJumpCond----------------------------------------------");
            // console.log(opJumpCond);
            return formula;
        }
        case MIROpTag.MIRJumpNone: {
            console.log("MIRJumpNone Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRVarLifetimeStart: {
            let opVarLifetimeStart = op as MIRVarLifetimeStart;
            typesSeen.set(section + "__" + opVarLifetimeStart.name, opVarLifetimeStart.rtype);
            // TODO: Here is where we include the type relation 
            // of variables
            return formula;
        }
        case MIROpTag.MIRVarLifetimeEnd: {
            console.log("MIRVarLifetimeEnd Not implemented yet");
            return formula;
        }
        case MIROpTag.MIRPhi: {
            let opPhi = op as MIRPhi;
            // console.log("Implementing MIRPhi-----------------------------");
            // console.log(opPhi);
            let targetName = section + "__" + opPhi.trgt.nameID;
            // TODO: Fix this using UnionType or a
            // clever approach. Currently is just set to 
            // be the IntType for the purpose of the 
            // max function demo
            typesSeen.set(targetName, "NSCore::Int");
            opPhi.src.forEach((value, key) => {
                value;
            });
            // let targetExpr = argumentToVarExpr(opPhi.trgt, section);
            return formula;
        }
        default:
            console.log("This might be a problem");
            return formula;
    }
}

// params is a sorted array of MIRFunctionParameter
// i.e. the first element corresponds to the first argument, ... and so on.
// Resolve names by prefixing section to every name encountered
function collectFormulas(ibody: Map<string, MIRBasicBlock>, section: string): FormulaExpr {
    const blocks = topologicalOrder(ibody);
    const flow = computeBlockLinks(ibody);
    const mapBlocks = new Map<string, MIRBasicBlock>();
    blocks.map(x => mapBlocks.set(x.label, x));
    let mapFormulas: Map<string, FormulaExpr> = new Map<string, FormulaExpr>();

    console.log("Blocks:-----------------------------------------------------------------------");
    console.log(blocks);
    console.log("More detailed Blocks:---------------------------------------------------------");
    blocks.map(x => console.log(x));
    console.log("More detailed++ Blocks:-------------------------------------------------------");
    blocks.map(x => console.log(x.jsonify()));
    console.log("Flow:-------------------------------------------------------------------------");
    console.log(flow);

    let changeFormula = false;
    for (let currentBlock of blocks) {
        let currentBlockName = currentBlock.label;
        // Important: according to the weakest precondition 
        // semantics currentBlocks.ops should be in reverse
        // let blockFormula = currentBlock.ops.reduce((a, b) => opToFormula(b, section, a), initialFormula);
        //---------------------------------------------------------------------------------------------
        // Process the formula for the individual block
        changeFormula = false
        let blockFormula = new PredicateExpr("true", []) as FormulaExpr;
        for (let op of currentBlock.ops) {
            if (!changeFormula) {
                changeFormula = true;
                blockFormula = opToFormula(op, section);
            }
            else {
                blockFormula = new AndExpr(blockFormula, opToFormula(op, section));
            }
        }
        //---------------------------------------------------------------------------------------------
        //---------------------------------------------------------------------------------------------
        // Extend to above formula with previous conditions
        let extendedBlockFormula = new PredicateExpr("true", []) as FormulaExpr;
        let flowBlock = flow.get(currentBlockName) as FlowLink;
        changeFormula = false;
        if (flowBlock.preds.size !== 0) {
            let flowBlockPred = Array.from(flowBlock.preds);
            for (let predLabel of flowBlockPred) {
                let predBlock = (mapBlocks.get(predLabel) as MIRBasicBlock);
                let lastIndex = predBlock.ops.length - 1;
                let lastOp = predBlock.ops[lastIndex];
                changeFormula = false;
                if (!changeFormula) {
                    if (lastOp instanceof MIRJumpCond) {
                        changeFormula = true;
                        let regName = lastOp.arg.nameID[0] == "#" ? "__" + lastOp.arg.nameID.slice(1) : lastOp.arg.nameID;
                        if (currentBlockName === lastOp.trueblock) {
                            extendedBlockFormula = new ImplExpr(new PredicateExpr(regName, []), blockFormula);
                        }
                        else {
                            extendedBlockFormula = new ImplExpr(new NegExpr(new PredicateExpr(regName, [])), blockFormula);
                        }
                    }
                    if (lastOp instanceof MIRJump) {
                    }
                }
                else {
                    if (lastOp instanceof MIRJumpCond) {
                        let regName = lastOp.arg.nameID[0] == "#" ? "__" + lastOp.arg.nameID.slice(1) : lastOp.arg.nameID;
                        let regPredicate = new PredicateExpr(regName, []);
                        if (currentBlockName === lastOp.trueblock) {
                            extendedBlockFormula = new AndExpr(extendedBlockFormula, new ImplExpr(regPredicate, blockFormula));
                        }
                        else {
                            extendedBlockFormula = new AndExpr(extendedBlockFormula, new ImplExpr(new NegExpr(regPredicate), blockFormula));
                        }
                    }
                    if (lastOp instanceof MIRJump) {
                    }
                }
            }
            if(changeFormula){
                mapFormulas.set(currentBlockName, extendedBlockFormula);
            }
        }
        else{
            mapFormulas.set(currentBlockName, blockFormula);
        }
        //---------------------------------------------------------------------------------------------
    }
    //---------------------------------------------------------------------------------------------
    // Collects all the formulas
    changeFormula = false;
    let result: FormulaExpr = new PredicateExpr("true", []);
    for (let formula of mapFormulas.values()) {
        if (!changeFormula) {
            changeFormula = true;
            result = formula;
        }
        else {
            result = new AndExpr(result, formula);
        }
    }
    return result;
    //---------------------------------------------------------------------------------------------
}

export { collectFormulas, typesSeen }