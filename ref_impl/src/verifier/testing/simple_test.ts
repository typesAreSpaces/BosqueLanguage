import { UnionType, IntType, TypeExpr, BoolType, NoneType } from "../type_expr"

let a = new UnionType(new Set<TypeExpr>([new BoolType(), new IntType(), new NoneType()]));
let b = new UnionType(new Set<TypeExpr>([new BoolType(), new IntType()]));

function subsetOf(a: UnionType, b: UnionType) {

    for(let element of a.elements){
        for(let element2 of b.elements){
            if(element.equalTo(element2)){
                
            }
        }
    }
}

console.log(subsetOf(a, b));


