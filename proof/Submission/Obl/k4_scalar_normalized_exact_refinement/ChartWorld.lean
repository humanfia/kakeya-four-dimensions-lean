import Submission.Obl.k4_scalar_normalized_exact_refinement.NormalizedWorld
import Submission.Obl.k4_scalar_normalized_exact_refinement.ChartSelection
import Submission.Obl.k4_scalar_normalized_exact_refinement.Spec

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open MeasureTheory Set
open k4_scalar_linear_critical_extremizers.Split
open scoped ENNReal

noncomputable section

def chartPrior (ν : Measure Line) (A : Set Line) (P : MvPolynomial (Fin 2) ℝ)
    (t₀ dt u v J δ : ℝ) : Measure Line :=
  (ν A)⁻¹ • (ν.restrict A).map (normalizeLine P t₀ dt u v J δ)

def chartEvent (C : Set (Line × ℝ)) (P : MvPolynomial (Fin 2) ℝ)
    (t₀ dt u v J δ : ℝ) : Set (Line × ℝ) :=
  (fun z : Line × ℝ => (normalizeLine P t₀ dt u v J δ z.1, (z.2 - t₀) / dt)) '' C

lemma normalization_coefficient_budget {N ε M : ℝ}
    (hN : 2 ≤ N) (hε : ε ≤ 1) (hM : 4 ≤ M) : 8 * N ^ ε ≤ N ^ M := by
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have h8 : (8 : ℝ) ≤ N ^ (3 : ℕ) := by
    calc
      8 = (2 : ℝ) ^ (3 : ℕ) := by norm_num
      _ ≤ N ^ (3 : ℕ) := by gcongr
  calc
    8 * N ^ ε ≤ N ^ (3 : ℕ) * N ^ (1 : ℝ) :=
      mul_le_mul h8 (Real.rpow_le_rpow_of_exponent_le hN1 hε)
        (Real.rpow_nonneg hN0.le _) (by positivity)
    _ = N ^ (4 : ℝ) := by rw [← Real.rpow_natCast N 3, ← Real.rpow_add hN0]; norm_num
    _ ≤ N ^ M := Real.rpow_le_rpow_of_exponent_le hN1 hM

/-- Fixed exponents certify every normalized world of a pruned chart. -/
lemma chart_normalized_world {p : Code} (hp : Spec.RawScalar p)
    {B M' D' k T n : ℕ} {r b h ε : ℝ}
    {γ : Fin n → Fin (W p k)} {j : Fin n → Fin (2 ^ T)}
    {A : Fin n → Set Line} {C : Fin n → Set (Line × ℝ)} {u v J : Fin n → ℝ}
    {P : Fin n → MvPolynomial (Fin 2) ℝ}
    {Λ : Fin (W p k) → ((Fin 2 → ℝ) × ℤ) → Finset (Fin n)}
    (hr : 0 ≤ r) (hε : ε ≤ 1)
    (hMcount : max (M p : ℝ) (B : ℝ) + 1 ≤ (M' : ℝ)) (hMfit : (4 : ℝ) ≤ M')
    (hMheight : (M p : ℝ) + 4 * h + 6 + ((B : ℝ) + 2) ≤ M')
    (hD : 2 * max (D p) B ≤ D')
    (hd : ChartData p B r b (h + ε) ε false k T n γ j A C u v J P Λ)
    (hprior : ∀ i, N p k ^ (-((B : ℝ) + 2)) ≤ (ν p k (γ i) (A i)).toReal)
    (i : Fin n) :
    k4_scalar_conditional_crop_worlds.WorldData (N p k ^ (M' : ℝ)) D' (8 * N p k ^ ε)
      (chartPrior (ν p k (γ i)) (A i) (P i)
        (((j i : ℕ) : ℝ) * ((2 : ℝ) ^ T)⁻¹) (((2 : ℝ) ^ T)⁻¹)
        (u i) (v i) (J i) (N p k ^ (-r)))
      (chartEvent (C i) (P i)
        (((j i : ℕ) : ℝ) * ((2 : ℝ) ^ T)⁻¹) (((2 : ℝ) ^ T)⁻¹)
        (u i) (v i) (J i) (N p k ^ (-r))) := by
  have hN : 2 ≤ N p k := hp.1.1 k
  have hN0 : 0 < N p k := by linarith
  have hN1 : 1 ≤ N p k := by linarith
  have hM : (M p : ℝ) ≤ M' := by linarith [le_max_left (M p : ℝ) (B : ℝ)]
  have hB : (B : ℝ) ≤ M' := by linarith [le_max_right (M p : ℝ) (B : ℝ)]
  have hw := hp.2 k
  let : IsProbabilityMeasure (ν p k (γ i)) := (hw.2.2.2.1 (γ i)).1
  have hν : k4_scalar_conditional_crop_worlds.PriorData (N p k ^ (M p : ℝ)) (D p)
      (ν p k (γ i)) := (hw.2.2.2.1 (γ i)).2.1
  obtain ⟨_, hJ, _, hJup, _, hP, _, hlabel, hFA, hFC, hfit, _⟩ := hd.2.2.2.2.2.1 i
  have hdt : 0 < ((2 : ℝ) ^ T)⁻¹ := by positivity
  have hdt1 : ((2 : ℝ) ^ T)⁻¹ ≤ 1 := by
    simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1) (one_le_pow₀ (by norm_num) : (1 : ℝ) ≤ 2 ^ T)
  have hδ : 0 < N p k ^ (-r) := Real.rpow_pos_of_pos hN0 _
  have hδ1 : N p k ^ (-r) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have hmass : ν p k (γ i) (A i) ≠ 0 := by
    intro hz
    have hh := hprior i
    rw [hz, ENNReal.toReal_zero] at hh
    exact not_le_of_gt (Real.rpow_pos_of_pos hN0 _) hh
  have hR : N p k ^ (M p : ℝ) ≤ N p k ^ (M' : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 hM
  have hRB : N p k ^ (B : ℝ) ≤ N p k ^ (M' : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 hB
  have hRC : 1 ≤ N p k ^ (B : ℝ) := Real.one_le_rpow hN1 (Nat.cast_nonneg B)
  have hCA : C i ⊆ A i ×ˢ Icc
      (((j i : ℕ) : ℝ) * ((2 : ℝ) ^ T)⁻¹)
      (((j i : ℕ) : ℝ) * ((2 : ℝ) ^ T)⁻¹ + ((2 : ℝ) ^ T)⁻¹) := by
    intro z hz
    simpa only [I, div_eq_mul_inv, add_mul, one_mul] using (hd.2.2.2.2.1 i hz).2
  have ht s (hs : s ∈ Icc (0 : ℝ) 1) :
      ((j i : ℕ) : ℝ) * ((2 : ℝ) ^ T)⁻¹ + ((2 : ℝ) ^ T)⁻¹ * s ∈ I T (j i) := by
    change _ ∈ Icc _ _
    simp only [div_eq_mul_inv, add_mul, one_mul]
    constructor <;> nlinarith [mul_nonneg hdt.le hs.1, mul_nonneg hdt.le (sub_nonneg.mpr hs.2)]
  have hworld := normalized_world_data (ν p k (γ i)) hν (A i) (C i)
    (hd.2.2.1 i).1 (hd.2.2.1 i).2 hmass hFA hFC (P i) hP
    (((j i : ℕ) : ℝ) * ((2 : ℝ) ^ T)⁻¹) (((2 : ℝ) ^ T)⁻¹)
    (u i) (v i) (J i) (N p k ^ (-r)) hdt hJ hδ
    (by linarith [Real.rpow_pos_of_pos hN0 (M p : ℝ)])
    ((normalization_format_count_bound hN).trans
      (Real.rpow_le_rpow_of_exponent_le hN1 hMcount)) hR hD hRC hRB
    ((Nat.mul_le_mul_left 2 (le_max_right (D p) B)).trans hD)
    ((normalized_prior_height_bound hN1 hε hdt hdt1 (by simpa using hd.1) hJ.le
      (by simpa only [div_eq_mul_inv] using hJup) hδ.le hδ1 (hprior i)).trans
      (Real.rpow_le_rpow_of_exponent_le hN1 hMheight))
    (Real.rpow_nonneg hN0.le _) (normalization_coefficient_budget hN hε hMfit)
    (fun l hl => (hlabel l hl).1.trans hRB) hCA (fun l hl s hs => hfit l hl _ (ht s hs))
  have he : ⇑(normalizeEquiv (P i) hP
      (((j i : ℕ) : ℝ) * ((2 : ℝ) ^ T)⁻¹) (((2 : ℝ) ^ T)⁻¹)
      (u i) (v i) (J i) (N p k ^ (-r)) hdt.ne' hJ.ne' hδ.ne') =
      normalizeLine (P i) (((j i : ℕ) : ℝ) * ((2 : ℝ) ^ T)⁻¹) (((2 : ℝ) ^ T)⁻¹)
        (u i) (v i) (J i) (N p k ^ (-r)) := funext (fun _ => normalizeEquiv_apply ..)
  have hevent : ((normalizeEquiv (P i) hP
      (((j i : ℕ) : ℝ) * ((2 : ℝ) ^ T)⁻¹) (((2 : ℝ) ^ T)⁻¹)
      (u i) (v i) (J i) (N p k ^ (-r)) hdt.ne' hJ.ne' hδ.ne').prodCongr
      (timeEquiv (((j i : ℕ) : ℝ) * ((2 : ℝ) ^ T)⁻¹) (((2 : ℝ) ^ T)⁻¹) hdt.ne')) '' C i =
      chartEvent (C i) (P i) (((j i : ℕ) : ℝ) * ((2 : ℝ) ^ T)⁻¹) (((2 : ℝ) ^ T)⁻¹)
        (u i) (v i) (J i) (N p k ^ (-r)) := by
    unfold chartEvent
    congr 1
    funext z
    apply Prod.ext
    · exact normalizeEquiv_apply ..
    · exact timeEquiv_apply ..
  simpa only [hevent, he, chartPrior] using hworld

lemma chart_selected_transport (ν : Measure Line) [SFinite ν]
    (E : Set (Line × ℝ)) (A : Set Line) (C : Set (Line × ℝ))
    (hC : MeasurableSet C) (hCA : C ⊆ A ×ˢ univ) (hCE : C ⊆ E)
    (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ dt u v J δ : ℝ) (hdt : 0 < dt) (hJ : J ≠ 0) (hδ : δ ≠ 0) :
    (((chartPrior ν A P t₀ dt u v J δ).prod volume).restrict
      (chartEvent C P t₀ dt u v J δ)) =
      (ENNReal.ofReal dt * ν A)⁻¹ •
        (((ν.prod volume).restrict E).restrict C).map
          (fun z : Line × ℝ => (normalizeLine P t₀ dt u v J δ z.1, (z.2 - t₀) / dt)) := by
  let e := normalizeEquiv P hP t₀ dt u v J δ hdt.ne' hJ hδ
  have he : (e : Line → Line) = normalizeLine P t₀ dt u v J δ :=
    funext (fun _ => normalizeEquiv_apply ..)
  have hprod : ⇑(e.prodCongr (timeEquiv t₀ dt hdt.ne')) =
      (fun z : Line × ℝ => (normalizeLine P t₀ dt u v J δ z.1, (z.2 - t₀) / dt)) := by
    funext z
    apply Prod.ext
    · exact normalizeEquiv_apply ..
    · exact timeEquiv_apply ..
  simpa only [chartPrior, chartEvent, he, hprod] using
    normalized_selected_transport_restrict ν E A C hC hCA hCE e t₀ dt hdt

end

end Submission.Obl.k4_scalar_normalized_exact_refinement
