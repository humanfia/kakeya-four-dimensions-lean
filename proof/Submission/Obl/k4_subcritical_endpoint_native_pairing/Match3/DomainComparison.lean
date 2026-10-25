/- Adapted from this LOT tree, obligation o218, session x0764, commit e1e41f8e737fdc1974cfdf32d18bbf69838b3ce8,
   Submission/Obl/k4_horizontal_endpoint_wide_return/Match3/DomainComparison.lean.
   Original source attributions are retained below. -/
/- Adapted from this LOT obligation, session x0764, Match3/DomainComparison.lean, commit2b232aca. -/
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3.GML3Law
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3.DomainCaps

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Full-time comparison on one domain

Paper, Lemma `a07:full-time-comparison`, the matching step: on a domain
`G × I = [t₀, t₀ + τ] × [p₀, p₀ + D] × [q₀, q₀ + D]` (a time block times a parameter square),
two finite lists of full-time predictors (`parameterPredictor h t p q`; for instance engine
labels `H₀` and native affine labels `𝓛 = nativeParam L v`) both fit the value `X` of every
event to `δ/2` at its parameters `(T, P, Q)`.  With

* sup bounds `E` of all predictors on the domain,
* floors `T_GI / A₀` of every label, `T_GI = τ D² V δ^d`,
* joint caps `V σ^d δm³` in parameter cells of side `δm` and value bins `σ ∈ [δ, 1]`
  (`param_cap_of_spatial_cap` produces them from the spatial joint caps),

`domain_comparison` bounds the mass of events whose two predictors differ by `≥ 10 M*`
somewhere on the box `|t - t_c| ≤ 4τ`, `|p - p_c| ≤ 4D`, `|q - q_c| ≤ 4D` (which contains the
domain), by `A (M*/δ)^{-η}` times the reference weights `(#ι₁ + #ι₂) T_GI` of the two lists.
The labels and their weights are the original ones; nothing is renormalized.
-/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3

open Set MeasureTheory

theorem q3E_toLp (a : Fin 10 → ℝ) (v : Fin 3 → ℝ) : q3E a (WithLp.toLp 2 v) = q3 a v := rfl

theorem abs_div_four_le_one {x c w : ℝ} (hw : 0 < w) (h : |x - c| ≤ 4 * w) :
    |(x - c) / (4 * w)| ≤ 1 := by
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 4 * w), div_le_one (by linarith)]
  exact h

/-- **Full-time comparison on one domain.** -/
theorem domain_comparison (hM : Matching) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) :
    ∃ η : ℝ, 0 < η ∧ ∃ R₀ : ℝ, 1 ≤ R₀ ∧
    ∀ (Ω : Type*) [MeasurableSpace Ω] (lam : Measure Ω) [IsFiniteMeasure lam]
      (ι₁ ι₂ : Type) [Fintype ι₁] [Fintype ι₂] [MeasurableSpace ι₁] [MeasurableSpace ι₂]
      [DiscreteMeasurableSpace ι₁] [DiscreteMeasurableSpace ι₂]
      (f₁ : Ω → ι₁) (f₂ : Ω → ι₂) (T P Q X : Ω → ℝ)
      (h₁ : ι₁ → Fin 6 → ℝ) (h₂ : ι₂ → Fin 6 → ℝ)
      (t₀ τ p₀ q₀ D δ δm V E A₀ A Mst : ℝ),
      Measurable f₁ → Measurable f₂ → Measurable T → Measurable P → Measurable Q →
      0 < τ → 0 < D → 0 < δ → δ ≤ 1 → 0 < δm → 0 < V → 1 ≤ E → 0 < A₀ →
      15360 * E * δm ≤ δ * τ → 15360 * E * δm ≤ δ * D →
      R₀ * δ ≤ Mst → 13720 ≤ A → 2000000 * A₀ * E ≤ A → A ≤ (Mst / δ) ^ η →
      (∀ᵐ ω ∂lam, T ω ∈ Icc t₀ (t₀ + τ) ∧ P ω ∈ Icc p₀ (p₀ + D) ∧ Q ω ∈ Icc q₀ (q₀ + D) ∧
        |X ω - parameterPredictor (h₁ (f₁ ω)) (T ω) (P ω) (Q ω)| ≤ δ / 2 ∧
        |X ω - parameterPredictor (h₂ (f₂ ω)) (T ω) (P ω) (Q ω)| ≤ δ / 2) →
      (∀ i, ∀ t ∈ Icc t₀ (t₀ + τ), ∀ p ∈ Icc p₀ (p₀ + D), ∀ q ∈ Icc q₀ (q₀ + D),
        |parameterPredictor (h₁ i) t p q| ≤ E) →
      (∀ j, ∀ t ∈ Icc t₀ (t₀ + τ), ∀ p ∈ Icc p₀ (p₀ + D), ∀ q ∈ Icc q₀ (q₀ + D),
        |parameterPredictor (h₂ j) t p q| ≤ E) →
      (∀ i, ENNReal.ofReal (τ * D ^ 2 * V * δ ^ d / A₀) ≤ lam {ω | f₁ ω = i}) →
      (∀ j, ENNReal.ofReal (τ * D ^ 2 * V * δ ^ d / A₀) ≤ lam {ω | f₂ ω = j}) →
      (∀ σ, δ ≤ σ → σ ≤ 1 → ∀ (c : Fin 3 → ℤ) (j : ℤ),
        lam {ω | (fun k => ⌊(![T ω, P ω, Q ω] : Fin 3 → ℝ) k / δm⌋) = c ∧ ⌊X ω / σ⌋ = j} ≤
          ENNReal.ofReal (V * σ ^ d * δm ^ 3)) →
      lam {ω | ∃ t p q : ℝ, |t - (t₀ + τ / 2)| ≤ 4 * τ ∧ |p - (p₀ + D / 2)| ≤ 4 * D ∧
          |q - (q₀ + D / 2)| ≤ 4 * D ∧
          10 * Mst ≤
            |parameterPredictor (h₁ (f₁ ω)) t p q - parameterPredictor (h₂ (f₂ ω)) t p q|} ≤
        ENNReal.ofReal (A * (Mst / δ) ^ (-η) *
          ((Fintype.card ι₁ + Fintype.card ι₂) * (τ * D ^ 2 * V * δ ^ d))) := by
  obtain ⟨η, hη, R₀, hR₀, H⟩ := gml3_of_law hM hd0 hd1
  refine ⟨η, hη, R₀, hR₀, ?_⟩
  intro Ω _ lam _ ι₁ ι₂ _ _ _ _ _ _ f₁ f₂ T P Q X h₁ h₂ t₀ τ p₀ q₀ D δ δm V E A₀ A Mst
    hf₁ hf₂ hT hP hQ hτ hD hδ hδ1 hδm hV hE1 hA₀ hmτ hmD hMst hA1 hA2 hA hgood hE₁ hE₂
    hfl₁ hfl₂ hcap
  have hE0 : 0 < E := by linarith
  set c₁ : ι₁ → Fin 10 → ℝ := fun i => normCoeffs t₀ τ p₀ q₀ D (h₁ i) with hc₁
  set c₂ : ι₂ → Fin 10 → ℝ := fun j => normCoeffs t₀ τ p₀ q₀ D (h₂ j) with hc₂
  set Tw := τ * D ^ 2 * V * δ ^ d with hTw
  set w := δ / (21504 * E) with hw
  have hq₁ : ∀ i t p q, q3 (c₁ i) (normVec t₀ τ p₀ q₀ D t p q) = parameterPredictor (h₁ i) t p q :=
    fun i t p q => q3_normCoeffs_normVec hτ.ne' hD.ne' _ t p q
  have hq₂ : ∀ j t p q, q3 (c₂ j) (normVec t₀ τ p₀ q₀ D t p q) = parameterPredictor (h₂ j) t p q :=
    fun j t p q => q3_normCoeffs_normVec hτ.ne' hD.ne' _ t p q
  have hgood₁ : ∀ᵐ ω ∂lam, T ω ∈ Icc t₀ (t₀ + τ) ∧ P ω ∈ Icc p₀ (p₀ + D) ∧
      Q ω ∈ Icc q₀ (q₀ + D) ∧
      |X ω - q3 (c₁ (f₁ ω)) (normVec t₀ τ p₀ q₀ D (T ω) (P ω) (Q ω))| ≤ δ / 2 := by
    filter_upwards [hgood] with ω h
    exact ⟨h.1, h.2.1, h.2.2.1, by rw [hq₁]; exact h.2.2.2.1⟩
  have hgood₂ : ∀ᵐ ω ∂lam, T ω ∈ Icc t₀ (t₀ + τ) ∧ P ω ∈ Icc p₀ (p₀ + D) ∧
      Q ω ∈ Icc q₀ (q₀ + D) ∧
      |X ω - q3 (c₂ (f₂ ω)) (normVec t₀ τ p₀ q₀ D (T ω) (P ω) (Q ω))| ≤ δ / 2 := by
    filter_upwards [hgood] with ω h
    exact ⟨h.1, h.2.1, h.2.2.1, by rw [hq₂]; exact h.2.2.2.2⟩
  have hcoef₁ : ∀ i k, |c₁ i k| ≤ 512 * E := fun i k => abs_normCoeffs_le hτ hD (hE₁ i) k
  have hcoef₂ : ∀ j k, |c₂ j k| ≤ 512 * E := fun j k => abs_normCoeffs_le hτ hD (hE₂ j) k
  have hδMst : δ ≤ Mst := by nlinarith
  -- jet counts at every scale `M ≥ M*`
  have hjet : ∀ (ι : Type) [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι]
      (f : Ω → ι) (c : ι → Fin 10 → ℝ), Measurable f →
      (∀ᵐ ω ∂lam, T ω ∈ Icc t₀ (t₀ + τ) ∧ P ω ∈ Icc p₀ (p₀ + D) ∧ Q ω ∈ Icc q₀ (q₀ + D) ∧
        |X ω - q3 (c (f ω)) (normVec t₀ τ p₀ q₀ D (T ω) (P ω) (Q ω))| ≤ δ / 2) →
      (∀ i k, |c i k| ≤ 512 * E) →
      (∀ i, ENNReal.ofReal (τ * D ^ 2 * V * δ ^ d / A₀) ≤ lam {ω | f ω = i}) →
      ∀ (r : Fin 10 → ℝ) (M : ℝ), Mst ≤ M →
        ((Finset.univ.filter (fun i => ∀ k, |c i k - r k| ≤ M)).card : ℝ) ≤
          A * (M / δ) ^ d := by
    intro ι _ _ _ f c hf hg hc hfl r M hM
    have hδM : δ ≤ M := hδMst.trans hM
    have hMδ : 0 ≤ (M / δ) ^ d := Real.rpow_nonneg (div_nonneg (hδ.le.trans hδM) hδ.le) d
    have hA' : 2000000 * A₀ * E * (M / δ) ^ d ≤ A * (M / δ) ^ d :=
      mul_le_mul_of_nonneg_right hA2 hMδ
    by_cases hME : M ≤ 512 * E
    · exact (jet_count lam f T P Q X c hf hτ hD hδ hδ1 hδm hV hE1 hA₀ hd0 hd1 hmτ hmD hg hc hfl
        hcap r hδM hME).trans hA'
    · push Not at hME
      have hall : (Finset.univ.filter (fun i => ∀ k, |c i k - r k| ≤ M)).card ≤
          (Finset.univ.filter (fun i => ∀ k, |c i k - (0 : Fin 10 → ℝ) k| ≤ 512 * E)).card := by
        apply Finset.card_le_card
        intro i _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.zero_apply, sub_zero]
        exact hc i
      have hb := jet_count lam f T P Q X c hf hτ hD hδ hδ1 hδm hV hE1 hA₀ hd0 hd1 hmτ hmD hg hc
        hfl hcap (0 : Fin 10 → ℝ) (M := 512 * E) (by linarith) le_rfl
      calc ((Finset.univ.filter (fun i => ∀ k, |c i k - r k| ≤ M)).card : ℝ)
          ≤ (Finset.univ.filter (fun i => ∀ k, |c i k - (0 : Fin 10 → ℝ) k| ≤ 512 * E)).card := by
            exact_mod_cast hall
        _ ≤ 2000000 * A₀ * E * (512 * E / δ) ^ d := hb
        _ ≤ 2000000 * A₀ * E * (M / δ) ^ d := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_right hME.le hδ.le) hd0
        _ ≤ A * (M / δ) ^ d := hA'
  -- cube ceilings
  have hcube : ∀ (ι : Type) (f : Ω → ι) (c : ι → Fin 10 → ℝ),
      (∀ᵐ ω ∂lam, T ω ∈ Icc t₀ (t₀ + τ) ∧ P ω ∈ Icc p₀ (p₀ + D) ∧ Q ω ∈ Icc q₀ (q₀ + D) ∧
        |X ω - q3 (c (f ω)) (normVec t₀ τ p₀ q₀ D (T ω) (P ω) (Q ω))| ≤ δ / 2) →
      (∀ i k, |c i k| ≤ 512 * E) →
      ∀ i (y : E3), lam {ω | f ω = i ∧
        y - (WithLp.toLp 2 (normVec t₀ τ p₀ q₀ D (T ω) (P ω) (Q ω)) : E3) ∈ cube w} ≤
        ENNReal.ofReal (A * Tw * w ^ 3) := by
    intro ι f c hg hc i y
    refine (cube_ceiling lam f T P Q X c hτ hD hδ hδ1 hδm hV hE1 hd0 hmτ hmD hg hc hcap i y).trans
      (ENNReal.ofReal_le_ofReal ?_)
    have : 0 ≤ Tw * w ^ 3 := by positivity
    nlinarith
  -- the matching lemma on the incidence law
  have hxm : Measurable (fun ω => (WithLp.toLp 2 (normVec t₀ τ p₀ q₀ D (T ω) (P ω) (Q ω)) : E3)) := by
    apply (PiLp.continuous_toLp 2 _).measurable.comp
    apply measurable_pi_iff.mpr
    intro k
    fin_cases k <;> simp only [normVec, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] <;> fun_prop
  have hw0 : 0 < w := by positivity
  have hw8 : w ≤ 1 / 8 := by
    rw [hw, div_le_iff₀ (by positivity)]; linarith
  have hwδ : 42 * (512 * E) * w ≤ δ := by
    rw [hw]; field_simp; linarith
  have hclose : ∀ᵐ ω ∂lam,
      ‖(WithLp.toLp 2 (normVec t₀ τ p₀ q₀ D (T ω) (P ω) (Q ω)) : E3)‖ ≤ 1 / 4 ∧
      |q3E (c₁ (f₁ ω)) (WithLp.toLp 2 (normVec t₀ τ p₀ q₀ D (T ω) (P ω) (Q ω))) -
        q3E (c₂ (f₂ ω)) (WithLp.toLp 2 (normVec t₀ τ p₀ q₀ D (T ω) (P ω) (Q ω)))| ≤ δ := by
    filter_upwards [hgood] with ω h
    obtain ⟨hTω, hPω, hQω, hfit₁, hfit₂⟩ := h
    refine ⟨norm_toLp_le (abs_normVec_le hτ hD hTω hPω hQω), ?_⟩
    rw [q3E_toLp, q3E_toLp, hq₁, hq₂]
    calc _ = |(parameterPredictor (h₁ (f₁ ω)) (T ω) (P ω) (Q ω) - X ω) +
          (X ω - parameterPredictor (h₂ (f₂ ω)) (T ω) (P ω) (Q ω))| := by ring_nf
      _ ≤ |parameterPredictor (h₁ (f₁ ω)) (T ω) (P ω) (Q ω) - X ω| +
          |X ω - parameterPredictor (h₂ (f₂ ω)) (T ω) (P ω) (Q ω)| := abs_add_le _ _
      _ ≤ δ / 2 + δ / 2 := by rw [abs_sub_comm] at hfit₁; exact add_le_add hfit₁ hfit₂
      _ = δ := by ring
  have hres := H Ω lam ι₁ ι₂ f₁ f₂
    (fun ω => (WithLp.toLp 2 (normVec t₀ τ p₀ q₀ D (T ω) (P ω) (Q ω)) : E3)) c₁ c₂
    (fun _ => Tw) (fun _ => Tw) δ Mst A (512 * E) w hf₁ hf₂ hxm hδ hMst (by linarith) hA
    hw0 hw8 hwδ (fun _ => by positivity) (fun _ => by positivity) hcoef₁ hcoef₂
    (hcube ι₁ f₁ c₁ hgood₁ hcoef₁) (hcube ι₂ f₂ c₂ hgood₂ hcoef₂)
    (hjet ι₁ f₁ c₁ hf₁ hgood₁ hcoef₁ hfl₁) (hjet ι₂ f₂ c₂ hf₂ hgood₂ hcoef₂ hfl₂) hclose
  -- from coefficient discrepancy to the physical box
  refine (measure_mono ?_).trans (hres.trans (le_of_eq ?_))
  · intro ω hω
    obtain ⟨t, p, q, ht, hp, hq, hbad⟩ := hω
    simp only [Set.mem_ofPred_eq]
    by_contra hlt
    push Not at hlt
    set v := normVec t₀ τ p₀ q₀ D t p q with hv
    have hv1 : ∀ k, |v k| ≤ 1 := by
      intro k
      fin_cases k <;> simp only [hv, normVec, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
      · exact abs_div_four_le_one hτ ht
      · exact abs_div_four_le_one hD hp
      · exact abs_div_four_le_one hD hq
    have hval : |q3 (c₁ (f₁ ω) - c₂ (f₂ ω)) v| ≤ 10 * cnorm3 (c₁ (f₁ ω) - c₂ (f₂ ω)) :=
      abs_q3_le (fun k => abs_le_cnorm3 _ k) hv1
    rw [q3_sub, hq₁, hq₂] at hval
    linarith
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring_nf

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3
