/-
x1077 (o295). The constants of the row-packet glue and the numerical facts it
needs, as one proposition `NumericsGoal` on the precision exponent `Ep`.

From the row packet's constant `Kc ≥ 2`:
* `Kint Kc = 64 Kc^202` is the constant of `Cartesian.frozen_field_long_fits`
  (strip width `Kc^-100`, velocities `≤ Kc`, density `16 Kc^2`);
* `AT C e Kc = C · Kint^e` bounds the coefficients of the interpolated field;
* `Kf M C e Kc = 8 (3M+1) Kc^4 AT` is the constant of the physical packet;
* `eta C e Kc` is the long-line threshold, which keeps the mass `≥ ref / Kf`.

`NumericsGoal` asks that `Ep` absorbs all of them, uniformly in `Kc ≥ 2`,
`0 < ζ ≤ 1` and `0 < a ≤ Kc h`: with `θ = (a/h) ζ^Ep / Kc^Ep`, the mesh `ε` and
the bin width `pv` (both `≤ θ / Kc^Ep`) and the fit error `θ (1 + 3 Kc AT)` lie
below the switching bounds of `Switch.frozen_packet_final_of_velocity_bins`.
-/
import Submission.Obl.k4_physical_row_packet_potential.Switch.PacketFinal

set_option autoImplicit false

namespace Submission.Obl.k4_physical_row_packet_potential.Glue

open Submission.Obl.k4_physical_row_packet_potential.Switch.PacketSwitching

noncomputable section

/-- The constant of the Cartesian field. -/
def Kint (Kc : ℝ) : ℝ := 64 * Kc ^ 202

/-- The coefficient bound of the interpolated field. -/
def AT (C : ℝ) (e : ℕ) (Kc : ℝ) : ℝ := C * Kint Kc ^ e

/-- The retained fraction `(1 - ηq)^3 - 2 ps` of the witness frame. -/
def c0 : ℝ := (99 / 100) ^ 3 - 2 * (1 / 2000000000000)

/-- The mass constant of the interpolated field. -/
def Ccomb (C : ℝ) (e : ℕ) (Kc : ℝ) : ℝ := Kc ^ 3 / c0 * AT C e Kc

/-- The constant of the physical potential packet. -/
def Kf (M : ℕ) (C : ℝ) (e : ℕ) (Kc : ℝ) : ℝ := 8 * (3 * (M : ℝ) + 1) * Kc ^ 4 * AT C e Kc

/-- The long-line threshold. -/
def eta (C : ℝ) (e : ℕ) (Kc : ℝ) : ℝ := 1 / (12 * Kc * Ccomb C e Kc)

/-- The numerical facts of the glue, uniformly in the packet's constants. -/
def NumericsGoal (M : ℕ) (d₁ C : ℝ) (e cNorm cCurl Ep : ℕ) : Prop :=
  ∀ Kc a h ζ : ℝ, 2 ≤ Kc → 0 < a → 0 < h → a ≤ Kc * h → 0 < ζ → ζ ≤ 1 →
    Kf M C e Kc ≤ Kc ^ Ep ∧ 30 * Kint Kc ^ 2 ≤ Kc ^ Ep ∧ AT C e Kc * Kc ≤ Kc ^ Ep ∧
    2 * Kc ^ 101 ≤ Kc ^ Ep ∧
    a / h * ζ ^ Ep / Kc ^ Ep / Kc ^ Ep ≤
      binWidth (3 * M) cNorm cCurl (Kf M C e Kc) (2 * Kc) a h ζ d₁ (AT C e Kc) ∧
    a / h * ζ ^ Ep / Kc ^ Ep / Kc ^ Ep ≤
      packetEpsBound (3 * M) cNorm cCurl (Kf M C e Kc) (2 * Kc) a h ζ d₁ (AT C e Kc) ∧
    a / h * ζ ^ Ep / Kc ^ Ep * (1 + 3 * Kc * AT C e Kc) ≤
      packetErrBound (3 * M) cNorm cCurl (Kf M C e Kc) (2 * Kc) a h ζ d₁ (eta C e Kc)

end

end Submission.Obl.k4_physical_row_packet_potential.Glue
