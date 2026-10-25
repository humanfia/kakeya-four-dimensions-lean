import Mathlib

/-! Adapted from: here:o223 (session x0777, branch x0777). -/

/-!
# Local algebra of a quadratic hidden test

A hidden test of total degree at most two is `G(p, w) = γ(p) + β(p) w + α w²` with `β` affine
and `γ` quadratic in the base point `p = (t, Z, Y)`. At a base point we record its local data:
the values `g = γ(p)`, `b = β(p)`, the gradients `gr = ∇γ(p)`, `br = ∇β` and the (constant,
symmetric) Hessian `H` of `γ`.

`sffB` is the bilinear form
`M(p)[U,V] = 2γ β_U β_V - β(β_U γ_V + γ_U β_V) + 2α γ_U γ_V + (β² - 4αγ) γ_UV`.
On the sheet `G = 0` with `g = G_w` one has `g³ D²f = -M`; along any line the value
`M[V,V]` is a combination of the line's own test values (`sff_line_identity`), so it is
bounded by the fit data of the line alone. With the horizontal frame `X = (1,0,-Z)`,
`Zf = (0,1,t)`, `Y = (0,0,1)`, the three vertical components of `M` are recovered from the
horizontal ones and their horizontal derivatives (`sff_recover_XY`, `sff_recover_YZ`,
`sff_recover_YY`); these are the Heisenberg commutator identities of the paper's Lemma 8.6,
written as polynomial identities in the local data. `tangent_plane_identity` evaluates the
test on the tangent plane of a sheet point.
-/

namespace Submission.Lib.K4QuadraticSheetCore

noncomputable section

/-- Dot product in three coordinates, written out. -/
def dot3 (u v : Fin 3 → ℝ) : ℝ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- A bilinear form with matrix `H`, written out. -/
def bil3 (H : Fin 3 → Fin 3 → ℝ) (u v : Fin 3 → ℝ) : ℝ :=
  u 0 * (H 0 0 * v 0 + H 0 1 * v 1 + H 0 2 * v 2) +
  u 1 * (H 1 0 * v 0 + H 1 1 * v 1 + H 1 2 * v 2) +
  u 2 * (H 2 0 * v 0 + H 2 1 * v 1 + H 2 2 * v 2)

/-- The projected second fundamental form at local data. -/
def sffB (a g b : ℝ) (gr br : Fin 3 → ℝ) (H : Fin 3 → Fin 3 → ℝ) (U V : Fin 3 → ℝ) : ℝ :=
  2 * g * dot3 br U * dot3 br V - b * (dot3 br U * dot3 gr V + dot3 gr U * dot3 br V) +
    2 * a * dot3 gr U * dot3 gr V + (b ^ 2 - 4 * a * g) * bil3 H U V

/-- Its derivative along `W` for constant `U, V` (the data of `β` affine, `γ` quadratic). -/
def sffD (a b : ℝ) (gr br : Fin 3 → ℝ) (H : Fin 3 → Fin 3 → ℝ) (W U V : Fin 3 → ℝ) : ℝ :=
  2 * dot3 gr W * dot3 br U * dot3 br V -
    dot3 br W * (dot3 br U * dot3 gr V + dot3 gr U * dot3 br V) -
    b * (dot3 br U * bil3 H W V + bil3 H W U * dot3 br V) +
    2 * a * (bil3 H W U * dot3 gr V + dot3 gr U * bil3 H W V) +
    (2 * b * dot3 br W - 4 * a * dot3 gr W) * bil3 H U V

/-- The discriminant `β² - 4αγ` and its derivative along `W`. -/
def discV (a g b : ℝ) : ℝ := b ^ 2 - 4 * a * g

def discD (a b : ℝ) (gr br : Fin 3 → ℝ) (W : Fin 3 → ℝ) : ℝ :=
  2 * b * dot3 br W - 4 * a * dot3 gr W

/-- The horizontal frame at a base point and the derivatives of its moving vectors. -/
def frX (p : Fin 3 → ℝ) : Fin 3 → ℝ := ![1, 0, -p 1]
def frZ (p : Fin 3 → ℝ) : Fin 3 → ℝ := ![0, 1, p 0]
def frY : Fin 3 → ℝ := ![0, 0, 1]
def dfrX (W : Fin 3 → ℝ) : Fin 3 → ℝ := ![0, 0, -W 1]
def dfrZ (W : Fin 3 → ℝ) : Fin 3 → ℝ := ![0, 0, W 0]

/-- A symmetric Hessian. -/
def SymH (H : Fin 3 → Fin 3 → ℝ) : Prop := H 1 0 = H 0 1 ∧ H 2 0 = H 0 2 ∧ H 2 1 = H 1 2

section Identities

variable (a g b : ℝ) (gr br : Fin 3 → ℝ) (H : Fin 3 → Fin 3 → ℝ)

/-- **Line identity.** For a line through `(p, w)` with base velocity `V` and hidden velocity
`w1`, write `G0, G1, G2` for the value and the first two time derivatives of the test along the
line, and `Gw0, Gw1` for the value and time derivative of its hidden derivative. Then the
projected form in direction `V` is a combination of these five line quantities. -/
theorem sff_line_identity (V : Fin 3 → ℝ) (w w1 : ℝ) (hH : SymH H) :
    let G0 := g + b * w + a * w ^ 2
    let G1 := dot3 gr V + dot3 br V * w + b * w1 + 2 * a * w * w1
    let G2 := bil3 H V V + 2 * dot3 br V * w1 + 2 * a * w1 ^ 2
    let Gw0 := b + 2 * a * w
    let Gw1 := dot3 br V + 2 * a * w1
    sffB a g b gr br H V V =
      Gw0 ^ 2 * G2 - 2 * Gw0 * G1 * Gw1 + 2 * a * G1 ^ 2 - 2 * G0 * (2 * a * G2 - Gw1 ^ 2) := by
  obtain ⟨h10, h20, h21⟩ := hH
  simp only [sffB, dot3, bil3, h10, h20, h21]
  ring

/-- Recovery of the mixed vertical component `M[X,Y]` from horizontal data. -/
theorem sff_recover_XY (p : Fin 3 → ℝ) (hH : SymH H) :
    6 * discV a g b * sffB a g b gr br H (frX p) frY =
      3 * (sffB a g b gr br H (frX p) (frX p) * discD a b gr br (frZ p) -
          sffB a g b gr br H (frX p) (frZ p) * discD a b gr br (frX p)) -
        2 * discV a g b *
          ((sffD a b gr br H (frZ p) (frX p) (frX p) +
              2 * sffB a g b gr br H (dfrX (frZ p)) (frX p)) -
            (sffD a b gr br H (frX p) (frX p) (frZ p) +
              sffB a g b gr br H (dfrX (frX p)) (frZ p) +
              sffB a g b gr br H (frX p) (dfrZ (frX p)))) := by
  obtain ⟨h10, h20, h21⟩ := hH
  simp only [sffB, sffD, discV, discD, dot3, bil3, frX, frZ, frY, dfrX, dfrZ,
    Matrix.cons_val, h10, h20, h21]
  ring

/-- Recovery of the mixed vertical component `M[Y,Zf]` from horizontal data. -/
theorem sff_recover_YZ (p : Fin 3 → ℝ) (hH : SymH H) :
    6 * discV a g b * sffB a g b gr br H frY (frZ p) =
      2 * discV a g b *
          ((sffD a b gr br H (frX p) (frZ p) (frZ p) +
              2 * sffB a g b gr br H (dfrZ (frX p)) (frZ p)) -
            (sffD a b gr br H (frZ p) (frX p) (frZ p) +
              sffB a g b gr br H (dfrX (frZ p)) (frZ p) +
              sffB a g b gr br H (frX p) (dfrZ (frZ p)))) -
        3 * (sffB a g b gr br H (frZ p) (frZ p) * discD a b gr br (frX p) -
          sffB a g b gr br H (frX p) (frZ p) * discD a b gr br (frZ p)) := by
  obtain ⟨h10, h20, h21⟩ := hH
  simp only [sffB, sffD, discV, discD, dot3, bil3, frX, frZ, frY, dfrX, dfrZ,
    Matrix.cons_val, h10, h20, h21]
  ring

/-- Recovery of the vertical component `M[Y,Y]` from the mixed ones and their horizontal
derivatives. -/
theorem sff_recover_YY (p : Fin 3 → ℝ) (hH : SymH H) :
    4 * discV a g b * sffB a g b gr br H frY frY =
      3 * (sffB a g b gr br H (frX p) frY * discD a b gr br (frZ p) -
          sffB a g b gr br H (frZ p) frY * discD a b gr br (frX p)) -
        2 * discV a g b *
          ((sffD a b gr br H (frZ p) (frX p) frY +
              sffB a g b gr br H (dfrX (frZ p)) frY) -
            (sffD a b gr br H (frX p) (frZ p) frY +
              sffB a g b gr br H (dfrZ (frX p)) frY)) := by
  obtain ⟨h10, h20, h21⟩ := hH
  simp only [sffB, sffD, discV, discD, dot3, bil3, frX, frZ, frY, dfrX, dfrZ,
    Matrix.cons_val, h10, h20, h21]
  ring

/-- **Tangent plane identity.** If `f` is a root of the test at the base point (local data
`g, b, gr, br, H`) with `G_w = b + 2αf = s ≠ 0`, the tangent plane
`L(p + u) = f - ((f br + gr) · u) / s` meets the quadratic test, at the displaced point with
local data given by exact Taylor expansion, in the value `M[u,u] / (2 s²)`. -/
theorem tangent_plane_identity (f s : ℝ) (u : Fin 3 → ℝ) (hH : SymH H)
    (hroot : g + b * f + a * f ^ 2 = 0) (hs : s = b + 2 * a * f) (hs0 : s ≠ 0) :
    let L := f - (f * dot3 br u + dot3 gr u) / s
    let gu := g + dot3 gr u + bil3 H u u / 2
    let bu := b + dot3 br u
    gu + bu * L + a * L ^ 2 = sffB a g b gr br H u u / (2 * s ^ 2) := by
  obtain ⟨h10, h20, h21⟩ := hH
  intro L gu bu
  have hg : g = -(b * f) - a * f ^ 2 := by linarith
  simp only [L, gu, bu, sffB, dot3, bil3, h10, h20, h21]
  rw [hg]
  field_simp
  rw [hs]
  ring

end Identities

end

end Submission.Lib.K4QuadraticSheetCore
