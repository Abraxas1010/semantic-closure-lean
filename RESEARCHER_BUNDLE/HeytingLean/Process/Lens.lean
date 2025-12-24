import HeytingLean.Process.Nucleus

/-!
Process lens wrapper exposing the kernel operator as the lens nucleus.
-/

namespace HeytingLean
namespace Process

def ProcessLensKernel := ProcessKernel

@[simp] def processLensKernel : ProcessLensKernel := kernel

end Process
end HeytingLean

