//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRBasicBlock, MIROpTag, MIRBinCmp, MIRArgument, MIROp, MIRRegisterArgument, MIRVarLifetimeStart, MIRVarStore, MIRReturnAssign, MIRJump, MIRJumpCond, MIRBinOp, MIRPhi } from "../compiler/mir_ops";
import { topologicalOrder, computeBlockLinks } from "../compiler/ir_info";
import { TypeExpr, IntType, BoolType, StringType, UninterpretedType, UnionType } from "../verifier/type_expr";
import { VarExpr, FuncExpr } from "../verifier/term_expr";
import { PredicateExpr, FormulaExpr, AndExpr, EqualityExpr } from "../verifier/formula_expr";

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
            if(typeName.length > 3){
                switch(typeName.substr(0, 4)) {
                    case "=int" : {
                        return new IntType();
                    }
                    case "=str" : {
                        return new StringType();
                    }
                    default : {
                        return new UninterpretedType(typeName);
                    }
                }
            }   
            else{
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
    switch (op.tag) {
        case MIROpTag.LoadConst:
        case MIROpTag.LoadConstTypedString:
        case MIROpTag.AccessNamespaceConstant:
        case MIROpTag.AccessConstField:
        case MIROpTag.LoadFieldDefaultValue: {
            return new PredicateExpr("notdone1", []);
        }
        case MIROpTag.AccessCapturedVariable: {
            return new PredicateExpr("notdone2", []);
        }
        case MIROpTag.AccessArgVariable: {
            return new PredicateExpr("notdone3", []);
        }
        case MIROpTag.AccessLocalVariable: {
            return new PredicateExpr("notdone4", []);
        }
        case MIROpTag.ConstructorPrimary: {
            return new PredicateExpr("notdone5", []);
        }
        case MIROpTag.ConstructorPrimaryCollectionEmpty: {
            return new PredicateExpr("notdone6", []);
        }
        case MIROpTag.ConstructorPrimaryCollectionSingletons: {
            return new PredicateExpr("notdone7", []);
        }
        case MIROpTag.ConstructorPrimaryCollectionCopies: {
            return new PredicateExpr("notdone8", []);
        }
        case MIROpTag.ConstructorPrimaryCollectionMixed: {
            return new PredicateExpr("notdone9", []);
        }
        case MIROpTag.ConstructorTuple: {
            return new PredicateExpr("notdone10", []);
        }
        case MIROpTag.ConstructorRecord: {
            return new PredicateExpr("notdone11", []);
        }
        case MIROpTag.ConstructorLambda: {
            return new PredicateExpr("notdone12", []);
        }
        case MIROpTag.CallNamespaceFunction: {
            return new PredicateExpr("notdone13", []);
        }
        case MIROpTag.CallStaticFunction: {
            return new PredicateExpr("notdone14", []);
        }
        case MIROpTag.MIRAccessFromIndex: {
            return new PredicateExpr("notdone15", []);
        }
        case MIROpTag.MIRProjectFromIndecies: {
            return new PredicateExpr("notdone16", []);
        }
        case MIROpTag.MIRAccessFromProperty: {
            return new PredicateExpr("notdone17", []);
        }
        case MIROpTag.MIRProjectFromProperties: {
            return new PredicateExpr("notdone18", []);
        }
        case MIROpTag.MIRAccessFromField: {
            return new PredicateExpr("notdone19", []);
        }
        case MIROpTag.MIRProjectFromFields: {
            return new PredicateExpr("notdone20", []);
        }
        case MIROpTag.MIRProjectFromTypeTuple: {
            return new PredicateExpr("notdone21", []);
        }
        case MIROpTag.MIRProjectFromTypeRecord: {
            return new PredicateExpr("notdone22", []);
        }
        case MIROpTag.MIRProjectFromTypeConcept: {
            return new PredicateExpr("notdone23", []);
        }
        case MIROpTag.MIRModifyWithIndecies: {
            return new PredicateExpr("notdone24", []);
        }
        case MIROpTag.MIRModifyWithProperties: {
            return new PredicateExpr("notdone25", []);
        }
        case MIROpTag.MIRModifyWithFields: {
            return new PredicateExpr("notdone26", []);
        }
        case MIROpTag.MIRStructuredExtendTuple: {
            return new PredicateExpr("notdone27", []);
        }
        case MIROpTag.MIRStructuredExtendRecord: {
            return new PredicateExpr("notdone28", []);
        }
        case MIROpTag.MIRStructuredExtendObject: {
            return new PredicateExpr("notdone29", []);
        }
        case MIROpTag.MIRInvokeKnownTarget: {
            return new PredicateExpr("notdone30", []);
        }
        case MIROpTag.MIRInvokeVirtualTarget: {
            return new PredicateExpr("notdone31", []);
        }
        case MIROpTag.MIRCallLambda: {
            return new PredicateExpr("notdone32", []);
        }
        case MIROpTag.MIRPrefixOp: {
            return new PredicateExpr("notdone33", []);
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
            return new PredicateExpr("notdone35", []);
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
            let regFormula = new EqualityExpr(new VarExpr(regName, new BoolType()), opFormula);
            return new AndExpr(opFormula, regFormula);
        }
        case MIROpTag.MIRRegAssign: {
            return new PredicateExpr("notdone37", []);
        }
        case MIROpTag.MIRTruthyConvert: {
            return new PredicateExpr("notdone38", []);
        }
        case MIROpTag.MIRVarStore: {
            let opVarStore = op as MIRVarStore;
            console.log("Implementing MIRVarStore--------------------------------------");
            console.log(opVarStore);
            console.log("The types seen so far");
            console.log(typesSeen);
            // TODO: Currently, the commented code, 
            // which is the right implementation,
            // doesn't work as expected due to 
            // some issues with the global 
            // variable typesSeen
            // return new EqualityExpr(
            //     argumentToVarExpr(opVarStore.src, section), 
            //     argumentToVarExpr(opVarStore.name, section));
            return new PredicateExpr("notdone39", []);
        }
        case MIROpTag.MIRReturnAssign: {
            let opReturnAssign = op as MIRReturnAssign;
            console.log("Implementing MIRReturnAssign--------------------------------------");
            console.log(opReturnAssign);
            let regName = section + "__" + opReturnAssign.name.nameID;
            let srcName = section + "__" + opReturnAssign.src.nameID;
            // The register Variable will have the same
            // type of the src Variable
            typesSeen.set(regName, typesSeen.get(srcName) as string);
            return new EqualityExpr(
                argumentToVarExpr(opReturnAssign.name, section), 
                argumentToVarExpr(opReturnAssign.src, section));
        }
        case MIROpTag.MIRAssert: {
            return new PredicateExpr("notdone41", []);
        }
        case MIROpTag.MIRCheck: {
            return new PredicateExpr("notdone42", []);
        }
        case MIROpTag.MIRDebug: {
            return new PredicateExpr("notdone43", []);
        }
        case MIROpTag.MIRJump: {
            let opJump = op as MIRJump;
            console.log("Implementing MIRJump--------------------------------------------------");
            console.log(opJump);
            return new PredicateExpr("notdone44", []);
        }
        case MIROpTag.MIRJumpCond: {
            let opJumpCond = op as MIRJumpCond;
            console.log("Implementing MIRJumpCond----------------------------------------------");
            console.log(opJumpCond);
            return new PredicateExpr("notdone45", []);
        }
        case MIROpTag.MIRJumpNone: {
            return new PredicateExpr("notdone46", []);
        }
        case MIROpTag.MIRVarLifetimeStart: {
            let opVarLifetimeStart = op as MIRVarLifetimeStart;
            typesSeen.set(section + "__" + opVarLifetimeStart.name, opVarLifetimeStart.rtype);
            // TODO: Here is where we include the type relation 
            // of variables
            return new PredicateExpr("almostdone47", []);
        }
        case MIROpTag.MIRVarLifetimeEnd: {
            return new PredicateExpr("notdone48", []);
        }
        case MIROpTag.MIRPhi: {
            let opPhi = op as MIRPhi;
            console.log("Implementing MIRPhi-----------------------------");
            console.log(opPhi);
            let targetName = section + "__" + opPhi.trgt.nameID;
            // TODO: Fix this using UnionType or a
            // clever approach. Currently is just set to 
            // be the IntType for the purpose of the 
            // max function demo
            typesSeen.set(targetName, "NSCore::Int");
            opPhi.src.forEach((value, key) => {
                console.log(value);



            });
            let targetExpr = argumentToVarExpr(opPhi.trgt, section);

            return new PredicateExpr("notdone49", []);
        }
        default:
            return new PredicateExpr("thismightbeaproblem", []);
    }
}

// params is a sorted array of MIRFunctionParameter
// i.e. the first element corresponds to the first argument, ... and so on.
// Resolve names by prefixing section to every name encountered
function collectFormulas(ibody: Map<string, MIRBasicBlock>, section: string): FormulaExpr {
    const blocks = topologicalOrder(ibody);
    const flow = computeBlockLinks(ibody);

    console.log("Blocks:-----------------------------------------------------------------------");
    console.log(blocks);
    console.log("More detailed Blocks:---------------------------------------------------------");
    blocks.map(x => console.log(x));
    console.log("More detailed++ Blocks:-------------------------------------------------------");
    blocks.map(x => console.log(x.jsonify()));
    console.log("Flow:-------------------------------------------------------------------------");
    console.log(flow);

    let formulass = blocks.map(block => block.ops.map(x => opToFormula(x, section)));
    // TODO: This is wrong and the logical formula should 
    // be built by traversing the flow graph in a breadth
    // first search manner

    

    return (formulass as FormulaExpr[][])
        .map(formulas => formulas
            .reduce((a, b) => new AndExpr(a, b)))
        .reduce((a, b) => new AndExpr(a, b));
}

export { collectFormulas, typesSeen } 