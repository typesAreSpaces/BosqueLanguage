#include "bsqruntime.h"
namespace BSQ
{
/*forward type decls*/
class nsmain__bazI4I;

/*forward function decls*/
BSQInt nsmain__mainI5I();

/*type decls*/
class nsmain__bazI4I : public BSQObject
{
public:
    BSQInt nsmain__bar2_fI0I;
    BSQInt nsmain__baz_gI1I;
    bool nsmain__baz_kI2I;

    nsmain__bazI4I(BSQInt f, BSQInt g, bool k) : BSQObject(MIRNominalTypeEnum::nsmain__bazI4I), nsmain__bar2_fI0I(f), nsmain__baz_gI1I(g), nsmain__baz_kI2I(k) { ; }
    virtual ~nsmain__bazI4I() {  }

    std::u32string display() const
    {
        BSQRefScope<2> _scope_I3I;
        return std::u32string(U"NSMain::Baz{ ") + Runtime::diagnostic_format(BSQ_BOX_VALUE_BSQINT(this->nsmain__bar2_fI0I, _scope_I3I, 0)) + std::u32string(U", ") + Runtime::diagnostic_format(BSQ_BOX_VALUE_BSQINT(this->nsmain__baz_gI1I, _scope_I3I, 1)) + std::u32string(U", ") + Runtime::diagnostic_format(BSQ_BOX_VALUE_BOOL(this->nsmain__baz_kI2I)) + std::u32string(U" }");
    }

    BSQInt get$nsmain__bar2_fI0I() { return this->nsmain__bar2_fI0I; };

    
};

/*typecheck decls*/


/*function decls*/
BSQInt nsmain__mainI5I()
{
    BSQRefScope<1> _scope_I3I;
    BSQInt __ir_ret__I8I; BSQInt _return_;
    nsmain__bazI4I* __tmp_0I6I; nsmain__bazI4I* eI7I;

    __tmp_0I6I = _scope_I3I.addAllocRef<0, nsmain__bazI4I>(new nsmain__bazI4I(BSQ_VALUE_POS_1, BSQInt(2), true));
    eI7I = __tmp_0I6I;
    __ir_ret__I8I = BSQ_VALUE_0;
    goto exit;

exit:
    _return_ = __ir_ret__I8I;
    return _return_;
}
}

using namespace BSQ;

/*main decl*/
int main(int argc, char** argv) {
    if(argc != 0 + 1) { fprintf(stderr, "Expected 0 arguments but got %i\n", argc - 1); exit(1); }

    std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;


  try {
     BSQRefScope<1> _scope_I3I;
    std::cout << conv.to_bytes(Runtime::diagnostic_format(BSQ_BOX_VALUE_BSQINT(nsmain__mainI5I(), _scope_I3I, 0))) << "\n";
    fflush(stdout);
    return 0;
  } catch (BSQAbort& abrt) HANDLE_BSQ_ABORT(abrt) 
}
