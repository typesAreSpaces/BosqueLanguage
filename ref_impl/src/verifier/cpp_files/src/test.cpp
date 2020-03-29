#include <iostream>
#include <z3++.h>

int main(){
  z3::context ctx;
  try {
    z3::expr input = mk_and(ctx.parse_file("/home/jose/Documents/GithubProjects/BosqueLanguage/ref_impl/src/verifier/cpp_files/smt_files/small_test.smt2"));
    // This is just an example that works for small_test.smt2
    auto quantified_formula = input.arg(1);
    unsigned num_patterns = Z3_get_quantifier_num_patterns(ctx, quantified_formula);
    for(unsigned i = 0; i < num_patterns; i++){
      auto pattern = z3::expr(ctx, Z3_pattern_to_ast(ctx, Z3_get_quantifier_pattern_ast(ctx, quantified_formula, i)));
      std::cout << pattern << std::endl;
    } 
  }
  catch(...){
    std::cout << "file not found" << std::endl;
  }
  return 0;
}
