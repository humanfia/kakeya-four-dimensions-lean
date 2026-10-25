import Submission.Obl.k4_matching_switching_target_certificate.ControlPrediction
import Submission.Obl.k4_matching_homogeneous_records.Encoding

noncomputable section

namespace Submission.Obl.k4_matching_switching_target_certificate

open Set
open Submission.Obl.k4_matching_homogeneous_records (StageType dyadicCenter)

/-- Choose a value for each record class, with an explicit fallback for unused classes. -/
def recordValue {α τ : Type*} (S : Set α) (F : α → ℕ) (g : α → τ) (fallback : τ)
    (a : ℕ) : τ :=
  Function.extend (fun x : S => F x) (fun x : S => g x) (fun _ => fallback) a

lemma recordValue_eq {α τ : Type*} {S : Set α} {F : α → ℕ} {g : α → τ}
    (h : ∀ x ∈ S, ∀ y ∈ S, F x = F y → g x = g y) (fallback : τ)
    {x : α} (hx : x ∈ S) : recordValue S F g fallback (F x) = g x := by
  have hf : (fun x : S => g x).FactorsThrough (fun x : S => F x) :=
    fun x y hxy => h x x.property y y.property hxy
  exact hf.extend_apply (fun _ => fallback) ⟨x, hx⟩

def colourValue {τ : Type*} (p : τ × τ) (κ : Bool) : τ := if κ then p.1 else p.2

/-- The reference-level bin data, replacing its active-order bin by the finer palette bin. -/
def paletteJet (J m : ℕ) (β : ℕ → ℝ) (N a b : ℝ) (data : StageType J)
    (pal : ℤ × ℤ) (κ : Bool) (j : ℕ) : ℝ :=
  if j = m then ((colourValue pal κ : ℤ) : ℝ) / N ^ (β m + b)
  else if hj : j ≤ J then
    ((colourValue (data.2 ⟨j, by omega⟩) κ : ℤ) : ℝ) / N ^ jetAccuracy (jetRadius J β) j a
  else 0

/-- The constant control determined by the coarse reference data, the palette and the frame. -/
def paletteControl (J m hz : ℕ) (β : ℕ → ℝ) (N a b ta frame : ℝ)
    (data : StageType J) (pal : ℤ × ℤ) (κ : Bool) : ℝ :=
  N ^ β m * ((∑ i ∈ Finset.range (J + 1 - m),
    paletteJet J m β N a b data pal κ (m + i) *
      (ta - ((data.1 : ℝ) + 1 / 2) / (2 : ℝ) ^ hz) ^ i / (i.factorial : ℝ)) - frame)

/-- Predict a control directly from the true reference jets and their floor bins. -/
def referenceControl (J m hz : ℕ) (β : ℕ → ℝ) (N a b ta frame : ℝ)
    (f₁ f₂ : ℝ → ℝ) (t : ℝ) (κ : Bool) : ℝ :=
  paletteControl J m hz β N a b ta frame
    (Int.floor (t * (2 : ℝ) ^ hz), fun j =>
      (Int.floor (N ^ jetAccuracy (jetRadius J β) j a * iteratedDeriv j f₁ (dyadicCenter hz t)),
       Int.floor (N ^ jetAccuracy (jetRadius J β) j a * iteratedDeriv j f₂ (dyadicCenter hz t))))
    (Int.floor (N ^ (β m + b) * iteratedDeriv m f₁ (dyadicCenter hz t)),
     Int.floor (N ^ (β m + b) * iteratedDeriv m f₂ (dyadicCenter hz t))) κ

lemma referenceControl_error {J m hz : ℕ} (hmJ : m ≤ J) {β : ℕ → ℝ}
    {N ε γ b a ta frame t : ℝ} (hN : 1 ≤ N)
    (hγ0 : γ ≤ ((J : ℝ) + 1 - (m : ℝ)) * jetRadius J β a - β m)
    (hγ : ∀ i : ℕ, 1 ≤ i → m + i ≤ J →
      γ ≤ jetAccuracy (jetRadius J β) (m + i) a + (i : ℝ) * jetRadius J β a - β m)
    (f₁ f₂ : ℝ → ℝ) (κ : Bool)
    (hf : ContDiffOn ℝ (J + 1 : ℕ) (if κ then f₁ else f₂) (Ioo (-1 : ℝ) 2))
    (hfB : ∀ x ∈ Icc (0 : ℝ) 1, |iteratedDeriv (J + 1) (if κ then f₁ else f₂) x| ≤ N ^ ε)
    (ht : t ∈ Ico (0 : ℝ) 1) (hta : ta ∈ Icc (0 : ℝ) 1)
    (hdist : |ta - dyadicCenter hz t| ≤ N ^ (-jetRadius J β a)) :
    |N ^ β m * (iteratedDeriv m (if κ then f₁ else f₂) ta - frame) -
        referenceControl J m hz β N a b ta frame f₁ f₂ t κ| ≤
      N ^ (-b) + (3 + N ^ ε) * N ^ (-γ) := by
  have hN0 : 0 < N := by linarith
  let data : StageType J :=
    (Int.floor (t * (2 : ℝ) ^ hz), fun j =>
      (Int.floor (N ^ jetAccuracy (jetRadius J β) j a * iteratedDeriv j f₁ (dyadicCenter hz t)),
       Int.floor (N ^ jetAccuracy (jetRadius J β) j a * iteratedDeriv j f₂ (dyadicCenter hz t))))
  let pal : ℤ × ℤ :=
    (Int.floor (N ^ (β m + b) * iteratedDeriv m f₁ (dyadicCenter hz t)),
     Int.floor (N ^ (β m + b) * iteratedDeriv m f₂ (dyadicCenter hz t)))
  let A := paletteJet J m β N a b data pal κ
  have hA0 : |iteratedDeriv m (if κ then f₁ else f₂) (dyadicCenter hz t) - A m| ≤
      N ^ (-(β m + b)) := by
    have hfloor := abs_sub_floor_rpow_le (N := N) (l := β m + b) hN0
      (y := iteratedDeriv m (if κ then f₁ else f₂) (dyadicCenter hz t))
    cases κ <;> simpa [A, paletteJet, colourValue, pal] using hfloor
  have hA : ∀ i : ℕ, 1 ≤ i → m + i ≤ J →
      |iteratedDeriv (m + i) (if κ then f₁ else f₂) (dyadicCenter hz t) - A (m + i)| ≤
        1 * N ^ (-jetAccuracy (jetRadius J β) (m + i) a) := by
    intro i hi hiJ
    have hne : m + i ≠ m := by omega
    have hi0 : i ≠ 0 := by omega
    have hfloor := abs_sub_floor_rpow_le (N := N) (l := jetAccuracy (jetRadius J β) (m + i) a) hN0
      (y := iteratedDeriv (m + i) (if κ then f₁ else f₂) (dyadicCenter hz t))
    cases κ <;> simpa [A, paletteJet, colourValue, data, hne, hi0, hiJ] using hfloor
  have h := control_prediction_error hmJ (K := 1) hN zero_le_one hγ0 hγ hf hfB
    (Submission.Obl.k4_matching_homogeneous_records.dyadicCenter_mem ht) hta hdist A hA0 hA
  have heq : N ^ β m * (iteratedDeriv m (if κ then f₁ else f₂) ta - frame) -
      referenceControl J m hz β N a b ta frame f₁ f₂ t κ =
      N ^ β m * (iteratedDeriv m (if κ then f₁ else f₂) ta -
        ∑ i ∈ Finset.range (J + 1 - m), A (m + i) *
          (ta - dyadicCenter hz t) ^ i / (i.factorial : ℝ)) := by
    simp only [referenceControl, paletteControl, A, data, pal, dyadicCenter]
    ring
  rw [heq]
  simpa using h

/-- The reference-level stage already contained in the coarse record's history. -/
def referenceStage {n₁ n₂ : ℕ} (J z q : ℕ) (β : ℕ → ℝ) (N : ℝ) (h : ℕ → ℕ)
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (x : (Fin n₁ × Fin n₂) × ℝ) : StageType J :=
  Submission.Obl.k4_matching_homogeneous_records.stageFromCell J f₁ f₂ h
    (fun v j => N ^ jetAccuracy (jetRadius J β) j ((v : ℝ) / (q : ℝ))) z
    (x.1, Int.floor (x.2 * (2 : ℝ) ^ h z))

def referencePalette {n₁ n₂ : ℕ} (m z q : ℕ) (β : ℕ → ℝ) (N : ℝ) (h : ℕ → ℕ)
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (x : (Fin n₁ × Fin n₂) × ℝ) : ℤ × ℤ :=
  (Int.floor (N ^ (β m + 6 / (q : ℝ)) * iteratedDeriv m (f₁ x.1.1) (dyadicCenter (h z) x.2)),
   Int.floor (N ^ (β m + 6 / (q : ℝ)) * iteratedDeriv m (f₂ x.1.2) (dyadicCenter (h z) x.2)))

/-- This control depends only on a coarse record, a palette value, a colour and the fixed frame. -/
def codedControl {n₁ n₂ : ℕ} (J m k z q : ℕ) (β : ℕ → ℝ) (N ta frame : ℝ)
    (h : ℕ → ℕ) (F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ)
    (S : Set ((Fin n₁ × Fin n₂) × ℝ))
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (code : ℕ) (pal : ℤ × ℤ) (κ : Bool) : ℝ :=
  paletteControl J m (h z) β N ((z : ℝ) / (q : ℝ)) (6 / (q : ℝ)) ta frame
    (recordValue S (F k) (referenceStage J z q β N h f₁ f₂) (0, fun _ => (0, 0)) code)
    pal κ

lemma codedControl_eq_referenceControl {n₁ n₂ J m k z q : ℕ} {β : ℕ → ℝ}
    {N ta frame : ℝ} {h : ℕ → ℕ} {F : ℕ → ((Fin n₁ × Fin n₂) × ℝ) → ℕ}
    {S : Set ((Fin n₁ × Fin n₂) × ℝ)}
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ)
    (hrec : ∀ x ∈ S, ∀ y ∈ S, F k x = F k y →
      Int.floor (x.2 * (2 : ℝ) ^ h z) = Int.floor (y.2 * (2 : ℝ) ^ h z) ∧
      ∀ j : ℕ, j ≤ J →
        Int.floor (N ^ jetAccuracy (jetRadius J β) j ((z : ℝ) / (q : ℝ)) *
          iteratedDeriv j (f₁ x.1.1) (dyadicCenter (h z) x.2)) =
        Int.floor (N ^ jetAccuracy (jetRadius J β) j ((z : ℝ) / (q : ℝ)) *
          iteratedDeriv j (f₁ y.1.1) (dyadicCenter (h z) y.2)) ∧
        Int.floor (N ^ jetAccuracy (jetRadius J β) j ((z : ℝ) / (q : ℝ)) *
          iteratedDeriv j (f₂ x.1.2) (dyadicCenter (h z) x.2)) =
        Int.floor (N ^ jetAccuracy (jetRadius J β) j ((z : ℝ) / (q : ℝ)) *
          iteratedDeriv j (f₂ y.1.2) (dyadicCenter (h z) y.2)))
    {x : (Fin n₁ × Fin n₂) × ℝ} (hx : x ∈ S) (κ : Bool) :
    codedControl J m k z q β N ta frame h F S f₁ f₂ (F k x)
        (referencePalette m z q β N h f₁ f₂ x) κ =
      referenceControl J m (h z) β N ((z : ℝ) / (q : ℝ)) (6 / (q : ℝ)) ta frame
        (f₁ x.1.1) (f₂ x.1.2) x.2 κ := by
  have hstage : ∀ x ∈ S, ∀ y ∈ S, F k x = F k y →
      referenceStage J z q β N h f₁ f₂ x = referenceStage J z q β N h f₁ f₂ y := by
    intro x hx y hy hxy
    obtain ⟨ht, hj⟩ := hrec x hx y hy hxy
    apply Prod.ext ht
    funext j
    exact Prod.ext (hj j (by omega)).1 (hj j (by omega)).2
  unfold codedControl
  rw [recordValue_eq hstage (0, fun _ => (0, 0)) hx]
  rfl

end Submission.Obl.k4_matching_switching_target_certificate
