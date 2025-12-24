import HeytingLean.Process.Syntax

/-!
Structural congruence ≡ for processes (explicit relation).
Rules: par comm/assoc, par identity with nil, and congruence under par.
-/

namespace HeytingLean
namespace Process

inductive Congr : Proc → Proc → Prop
| refl  (P) : Congr P P
| symm  {P Q} : Congr P Q → Congr Q P
| trans {P Q R} : Congr P Q → Congr Q R → Congr P R
| par_comm (P Q) : Congr (Proc.parr P Q) (Proc.parr Q P)
| par_assoc (P Q R) : Congr (Proc.parr (Proc.parr P Q) R) (Proc.parr P (Proc.parr Q R))
| par_nil_left  (P) : Congr (Proc.parr Proc.nil P) P
| par_nil_right (P) : Congr (Proc.parr P Proc.nil) P
| par_congr_left  {P P' Q} : Congr P P' → Congr (Proc.parr P Q) (Proc.parr P' Q)
| par_congr_right {P Q Q'} : Congr Q Q' → Congr (Proc.parr P Q) (Proc.parr P Q')

infix:50 " ≡ " => Congr

end Process
end HeytingLean

