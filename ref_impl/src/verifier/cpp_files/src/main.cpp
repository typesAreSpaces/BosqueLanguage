#include <iostream>
#include "GraphFormulas.h"

int main(){
  z3::context ctx;
  try { 
    GraphFormulas test("/home/jose/Documents/GithubProjects/BosqueLanguage/ref_impl/src/verifier/cpp_files/smt_files/small_test.smt2");
    //GraphFormulas test("/home/jose/Documents/GithubProjects/BosqueLanguage/ref_impl/src/verifier/cpp_files/smt_files/test.smt2");
  }
  catch(Z3_error_code e){
    std::cout << e << std::endl;
  }
  return 0;
}
