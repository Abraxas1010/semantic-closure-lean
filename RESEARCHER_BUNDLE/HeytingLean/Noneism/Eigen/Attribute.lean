import Lean

namespace HeytingLean
namespace Noneism
namespace Eigen

open Lean Elab

namespace Attr

def eigencomputableGetParam (_decl : Name) (stx : Syntax) : AttrM Name := do
  match stx with
  | `(attr| eigencomputable $dyn:ident) => return dyn.getId
  | _ => throwError "unexpected eigencomputable attribute argument"

initialize eigencomputableAttr : ParametricAttribute Name ←
  registerParametricAttribute {
    name := `eigencomputable
    descr := "Mark a declaration as eigencomputable (records a dynamics name)."
    getParam := eigencomputableGetParam
  }

def eigencomputableDynamicsName? (env : Environment) (decl : Name) : Option Name :=
  eigencomputableAttr.getParam? env decl

end Attr

end Eigen
end Noneism
end HeytingLean

