/- Adapted from this LOT tree, obligation o218, session x0764, commit e1e41f8e737fdc1974cfdf32d18bbf69838b3ce8,
   Submission/Obl/k4_horizontal_endpoint_wide_return/Match3/DomainCaps.lean.
   Original source attributions are retained below. -/
/- Adapted from this LOT obligation, session x0764, Match3/DomainCaps.lean, commit2b232aca. -/
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3.Jitter3
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3.Domain
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3.RectCaps

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Cube ceilings and jet counts on a comparison domain

On a comparison domain `[t₀, t₀ + τ] × [p₀, p₀ + D] × [q₀, q₀ + D]` consider a finite measure
`λ` of events with parameters `(T, P, Q)` and value `X`, a finite list of labels `f : Ω → ι`
whose normalized quadratic predictors `c i` (coefficients `≤ 512 E`) fit `X` to `δ/2` at the
event's normalized parameters, and joint caps of `λ` in parameter cells of side `δm` and value
bins of every width `σ ∈ [δ, 1]`:
`λ {cell = c, ⌊X/σ⌋ = j} ≤ V σ^d δm³`.

* `cube_ceiling`: the events of one label whose normalized base point lies in a cube of side `w`
  have mass `≤ 13720 T w³`, `T = τ D² V δ^d`, at `w = δ / (21504 E)`;
* `jet_count`: if moreover every label has mass `≥ T / A₀`, at most `2·10⁶ A₀ E (M/δ)^d` labels
  have coefficients within `M` of any given vector, `δ ≤ M ≤ 512 E`.

These are the cube-ceiling and jet-count hypotheses of the three-dimensional matching lemma
(paper, Lemma `a07:full-time-comparison`: index-base marginals obey `K T_{GI}` times box-uniform
by the joint cap near the graph, and list counts are `≤ K (M₀/a₀)^d` by the floors under the cap
near a common graph).
-/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3

open Set MeasureTheory

theorem abs_sub_div_le {a b c w δm : ℝ} (hw : 0 < w) (h : |a - b| ≤ δm) :
    |(a - c) / (4 * w) - (b - c) / (4 * w)| ≤ δm / (4 * w) := by
  rw [← sub_div, show a - c - (b - c) = a - b by ring, abs_div,
    abs_of_pos (by linarith : (0 : ℝ) < 4 * w)]
  exact div_le_div_of_nonneg_right h (by linarith)

/-- Moving a point by `δm` moves its normalized coordinates by at most `δm/(4τ) + δm/(4D)`. -/
theorem normVec_sub_le {t₀ τ p₀ q₀ D δm : ℝ} (hτ : 0 < τ) (hD : 0 < D) {x y : Fin 3 → ℝ}
    (hxy : ∀ i, |x i - y i| ≤ δm) (k : Fin 3) :
    |normVec t₀ τ p₀ q₀ D (x 0) (x 1) (x 2) k - normVec t₀ τ p₀ q₀ D (y 0) (y 1) (y 2) k| ≤
      δm / (4 * τ) + δm / (4 * D) := by
  have hδm : 0 ≤ δm := (abs_nonneg _).trans (hxy 0)
  have hτ' : 0 ≤ δm / (4 * τ) := div_nonneg hδm (by linarith)
  have hD' : 0 ≤ δm / (4 * D) := div_nonneg hδm (by linarith)
  fin_cases k <;> simp only [normVec, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  · linarith [abs_sub_div_le (c := t₀ + τ / 2) hτ (hxy 0)]
  · linarith [abs_sub_div_le (c := p₀ + D / 2) hD (hxy 1)]
  · linarith [abs_sub_div_le (c := q₀ + D / 2) hD (hxy 2)]

/-- The offset `q3 g ∘ normVec` moves by at most `15 B ρ` over a cell of side `δm`. -/
theorem offset_close {t₀ τ p₀ q₀ D δm B : ℝ} (hτ : 0 < τ) (hD : 0 < D) {g : Fin 10 → ℝ}
    (hg : ∀ k, |g k| ≤ B) {x y : Fin 3 → ℝ}
    (hx : ∀ k, |normVec t₀ τ p₀ q₀ D (x 0) (x 1) (x 2) k| ≤ 1 / 8)
    (hxy : ∀ i, |x i - y i| ≤ δm) (hρ : δm / (4 * τ) + δm / (4 * D) ≤ 7 / 8) :
    |q3 g (normVec t₀ τ p₀ q₀ D (x 0) (x 1) (x 2)) - q3 g (normVec t₀ τ p₀ q₀ D (y 0) (y 1) (y 2))|
      ≤ 15 * B * (δm / (4 * τ) + δm / (4 * D)) := by
  apply abs_q3_sub_le hg
  · intro i; linarith [hx i]
  · intro i
    have h1 := normVec_sub_le (t₀ := t₀) (p₀ := p₀) (q₀ := q₀) hτ hD hxy i
    have h2 := hx i
    have : |normVec t₀ τ p₀ q₀ D (y 0) (y 1) (y 2) i| ≤
        |normVec t₀ τ p₀ q₀ D (x 0) (x 1) (x 2) i| +
          |normVec t₀ τ p₀ q₀ D (x 0) (x 1) (x 2) i - normVec t₀ τ p₀ q₀ D (y 0) (y 1) (y 2) i| := by
      have := abs_sub (normVec t₀ τ p₀ q₀ D (x 0) (x 1) (x 2) i)
        (normVec t₀ τ p₀ q₀ D (x 0) (x 1) (x 2) i - normVec t₀ τ p₀ q₀ D (y 0) (y 1) (y 2) i)
      simpa using this
    linarith
  · exact normVec_sub_le hτ hD hxy

section Caps

variable {Ω : Type*} [MeasurableSpace Ω] (lam : Measure Ω) {ι : Type} (f : Ω → ι)
  (T P Q X : Ω → ℝ) (c : ι → Fin 10 → ℝ) {t₀ τ p₀ q₀ D δ δm V E d : ℝ}

/-- The good events: parameters in the domain and value fitted by the label's predictor. -/
def goodSet (t₀ τ p₀ q₀ D δ : ℝ) : Set Ω :=
  {ω | T ω ∈ Icc t₀ (t₀ + τ) ∧ P ω ∈ Icc p₀ (p₀ + D) ∧ Q ω ∈ Icc q₀ (q₀ + D) ∧
    |X ω - q3 (c (f ω)) (normVec t₀ τ p₀ q₀ D (T ω) (P ω) (Q ω))| ≤ δ / 2}

theorem goodSet_compl
    (hgood : ∀ᵐ ω ∂lam, T ω ∈ Icc t₀ (t₀ + τ) ∧ P ω ∈ Icc p₀ (p₀ + D) ∧
      Q ω ∈ Icc q₀ (q₀ + D) ∧
      |X ω - q3 (c (f ω)) (normVec t₀ τ p₀ q₀ D (T ω) (P ω) (Q ω))| ≤ δ / 2) :
    lam (goodSet f T P Q X c t₀ τ p₀ q₀ D δ)ᶜ = 0 := by
  rw [goodSet, Set.compl_ofPred]
  exact ae_iff.mp hgood

theorem rho_le (hτ : 0 < τ) (hD : 0 < D) (hδ : 0 < δ) (hE1 : 1 ≤ E)
    (hmτ : 15360 * E * δm ≤ δ * τ) (hmD : 15360 * E * δm ≤ δ * D) :
    δm / (4 * τ) + δm / (4 * D) ≤ δ / (30720 * E) := by
  have hE0 : 0 < E := by linarith
  have h1 : δm / (4 * τ) ≤ δ / (61440 * E) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h2 : δm / (4 * D) ≤ δ / (61440 * E) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  have h3 : δ / (61440 * E) + δ / (61440 * E) = δ / (30720 * E) := by
    field_simp; ring
  linarith

/-- **Cube ceilings.** The events of one label whose normalized base point lies in the cube
`y - [0, w]³` weigh at most `13720 (τ D² V δ^d) w³`. -/
theorem cube_ceiling (hτ : 0 < τ) (hD : 0 < D) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδm : 0 < δm)
    (hV : 0 < V) (hE1 : 1 ≤ E) (hd0 : 0 ≤ d)
    (hmτ : 15360 * E * δm ≤ δ * τ) (hmD : 15360 * E * δm ≤ δ * D)
    (hgood : ∀ᵐ ω ∂lam, T ω ∈ Icc t₀ (t₀ + τ) ∧ P ω ∈ Icc p₀ (p₀ + D) ∧
      Q ω ∈ Icc q₀ (q₀ + D) ∧
      |X ω - q3 (c (f ω)) (normVec t₀ τ p₀ q₀ D (T ω) (P ω) (Q ω))| ≤ δ / 2)
    (hc : ∀ i k, |c i k| ≤ 512 * E)
    (hcap : ∀ σ, δ ≤ σ → σ ≤ 1 → ∀ (cc : Fin 3 → ℤ) (j : ℤ),
      lam {ω | (fun k => ⌊(![T ω, P ω, Q ω] : Fin 3 → ℝ) k / δm⌋) = cc ∧ ⌊X ω / σ⌋ = j} ≤
        ENNReal.ofReal (V * σ ^ d * δm ^ 3))
    (i : ι) (y : E3) :
    lam {ω | f ω = i ∧
        y - (WithLp.toLp 2 (normVec t₀ τ p₀ q₀ D (T ω) (P ω) (Q ω)) : E3) ∈
          cube (δ / (21504 * E))} ≤
      ENNReal.ofReal (13720 * (τ * D ^ 2 * V * δ ^ d) * (δ / (21504 * E)) ^ 3) := by
  set w := δ / (21504 * E) with hwdef
  have hE0 : 0 < E := by linarith
  have hw0 : 0 < w := by positivity
  set G := goodSet f T P Q X c t₀ τ p₀ q₀ D δ with hGdef
  have hGc : lam Gᶜ = 0 := goodSet_compl lam f T P Q X c hgood
  set ρ := δm / (4 * τ) + δm / (4 * D) with hρdef
  have hρ : ρ ≤ δ / (30720 * E) := rho_le hτ hD hδ hE1 hmτ hmD
  have hρ0 : 0 ≤ ρ := by positivity
  set θ := 15 * (512 * E) * ρ with hθdef
  have hθ : θ ≤ δ / 2 := by
    have : 15 * (512 * E) * ρ ≤ 15 * (512 * E) * (δ / (30720 * E)) :=
      mul_le_mul_of_nonneg_left hρ (by positivity)
    have h2 : 15 * (512 * E) * (δ / (30720 * E)) = δ / 4 := by field_simp; ring
    linarith
  have hθ0 : 0 ≤ θ := by positivity
  have hρ78 : ρ ≤ 7 / 8 := by
    have : δ / (30720 * E) ≤ 7 / 8 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  -- the cell side is below the box half-widths
  have hmw : δm ≤ 2 * τ * w ∧ δm ≤ 2 * D * w := by
    constructor
    · rw [hwdef, show 2 * τ * (δ / (21504 * E)) = δ * τ / (10752 * E) by field_simp; ring,
        le_div_iff₀ (by positivity)]
      nlinarith
    · rw [hwdef, show 2 * D * (δ / (21504 * E)) = δ * D / (10752 * E) by field_simp; ring,
        le_div_iff₀ (by positivity)]
      nlinarith
  set S := {ω | f ω = i ∧
    y - (WithLp.toLp 2 (normVec t₀ τ p₀ q₀ D (T ω) (P ω) (Q ω)) : E3) ∈ cube w} with hSdef
  rw [← measure_inter_conull (s := S) hGc]
  have hcap' := hcap δ le_rfl hδ1
  have key := rect_slab_cap lam (fun ω => ![T ω, P ω, Q ω]) X
    (fun y' => q3 (c i) (normVec t₀ τ p₀ q₀ D (y' 0) (y' 1) (y' 2)) - δ / 2) (S ∩ G)
    (W := δ) (θ := θ) (L := V * δ ^ d)
    ![t₀ + τ / 2 + 4 * τ * (y 0 - w / 2), p₀ + D / 2 + 4 * D * (y 1 - w / 2),
      q₀ + D / 2 + 4 * D * (y 2 - w / 2)]
    ![2 * τ * w, 2 * D * w, 2 * D * w] hδm hδ hθ0 hδ.le
    (by
      intro k
      fin_cases k
      · exact hmw.1
      · exact hmw.2
      · exact hmw.2)
    (by positivity)
    (by
      intro z hz y' hy'
      obtain ⟨hzT, hzP, hzQ, -⟩ := hz.2
      rw [sub_sub_sub_cancel_right]
      exact offset_close hτ hD (hc i)
        (fun k => abs_normVec_le hτ hD hzT hzP hzQ k) hy' hρ78)
    (by
      intro z hz
      obtain ⟨⟨hfi, hcube⟩, hzT, hzP, hzQ, hfit⟩ := hz
      rw [hfi] at hfit
      refine ⟨?_, ?_, ?_⟩
      · have hk : ∀ k, (y k - w ≤ normVec t₀ τ p₀ q₀ D (T z) (P z) (Q z) k) ∧
            (normVec t₀ τ p₀ q₀ D (T z) (P z) (Q z) k ≤ y k) := by
          intro k
          have := hcube k
          simp only [PiLp.sub_apply, Set.mem_Icc] at this
          constructor <;> linarith [this.1, this.2]
        obtain ⟨h0, h1, h2⟩ := normVec_unnorm (t₀ := t₀) (p₀ := p₀) (q₀ := q₀) (t := T z)
          (p := P z) (q := Q z) hτ.ne' hD.ne'
        intro k
        fin_cases k
        · simp only [Fin.zero_eta, Matrix.cons_val_zero]
          obtain ⟨hl, hu⟩ := hk 0
          rw [abs_le]; constructor <;> nlinarith
        · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
          obtain ⟨hl, hu⟩ := hk 1
          rw [abs_le]; constructor <;> nlinarith
        · simp only [Fin.reduceFinMk, Matrix.cons_val]
          obtain ⟨hl, hu⟩ := hk 2
          rw [abs_le]; constructor <;> nlinarith
      · have := (abs_le.mp hfit).1
        change q3 (c i) (normVec t₀ τ p₀ q₀ D (T z) (P z) (Q z)) - δ / 2 ≤ X z
        linarith
      · have := (abs_le.mp hfit).2
        change X z ≤ q3 (c i) (normVec t₀ τ p₀ q₀ D (T z) (P z) (Q z)) - δ / 2 + δ
        linarith)
    (by
      intro cc j
      have := hcap' cc j
      simpa only [mul_assoc] using this)
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  have hfac : (δ + 2 * θ) / δ + 2 ≤ 5 := by
    rw [div_add' _ _ _ hδ.ne', div_le_iff₀ hδ]; linarith
  have hVd : 0 ≤ V * δ ^ d := by positivity
  have hbox : 0 ≤ 2 * τ * w * (2 * D * w) * (2 * D * w) := by positivity
  calc 343 * (2 * τ * w * (2 * D * w) * (2 * D * w)) * ((δ + 2 * θ) / δ + 2) * (V * δ ^ d)
      ≤ 343 * (2 * τ * w * (2 * D * w) * (2 * D * w)) * 5 * (V * δ ^ d) := by gcongr
    _ = 13720 * (τ * D ^ 2 * V * δ ^ d) * w ^ 3 := by ring

/-- **Jet counts.** If every label has mass at least `T / A₀`, `T = τ D² V δ^d`, then at most
`2·10⁶ A₀ E (M/δ)^d` labels have coefficients within `M` of a given vector `g`,
for `δ ≤ M ≤ 512 E`. -/
theorem jet_count [Fintype ι] [MeasurableSpace ι] [DiscreteMeasurableSpace ι] {A₀ : ℝ}
    (hf : Measurable f) (hτ : 0 < τ) (hD : 0 < D) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδm : 0 < δm)
    (hV : 0 < V) (hE1 : 1 ≤ E) (hA₀ : 0 < A₀) (hd0 : 0 ≤ d) (hd1 : d < 1)
    (hmτ : 15360 * E * δm ≤ δ * τ) (hmD : 15360 * E * δm ≤ δ * D)
    (hgood : ∀ᵐ ω ∂lam, T ω ∈ Icc t₀ (t₀ + τ) ∧ P ω ∈ Icc p₀ (p₀ + D) ∧
      Q ω ∈ Icc q₀ (q₀ + D) ∧
      |X ω - q3 (c (f ω)) (normVec t₀ τ p₀ q₀ D (T ω) (P ω) (Q ω))| ≤ δ / 2)
    (hc : ∀ i k, |c i k| ≤ 512 * E)
    (hfloor : ∀ i, ENNReal.ofReal (τ * D ^ 2 * V * δ ^ d / A₀) ≤ lam {ω | f ω = i})
    (hcap : ∀ σ, δ ≤ σ → σ ≤ 1 → ∀ (cc : Fin 3 → ℤ) (j : ℤ),
      lam {ω | (fun k => ⌊(![T ω, P ω, Q ω] : Fin 3 → ℝ) k / δm⌋) = cc ∧ ⌊X ω / σ⌋ = j} ≤
        ENNReal.ofReal (V * σ ^ d * δm ^ 3))
    (g : Fin 10 → ℝ) {M : ℝ} (hδM : δ ≤ M) (hME : M ≤ 512 * E) :
    ((Finset.univ.filter (fun i => ∀ k, |c i k - g k| ≤ M)).card : ℝ) ≤
      2000000 * A₀ * E * (M / δ) ^ d := by
  set S := Finset.univ.filter (fun i => ∀ k, |c i k - g k| ≤ M) with hSdef
  have hE0 : 0 < E := by linarith
  have hM0 : 0 < M := hδ.trans_le hδM
  have hRHS : 0 ≤ 2000000 * A₀ * E * (M / δ) ^ d := by
    have : 0 ≤ (M / δ) ^ d := Real.rpow_nonneg (div_nonneg hM0.le hδ.le) d
    have : 0 ≤ 2000000 * A₀ * E := by positivity
    positivity
  rcases S.eq_empty_or_nonempty with hSe | ⟨i₀, hi₀⟩
  · rw [hSe, Finset.card_empty, Nat.cast_zero]; exact hRHS
  have hi₀' := (Finset.mem_filter.mp hi₀).2
  have hg : ∀ k, |g k| ≤ 1024 * E := by
    intro k
    have h1 := hi₀' k
    have h2 := hc i₀ k
    have : |g k| ≤ |c i₀ k| + |c i₀ k - g k| := by
      calc |g k| = |c i₀ k - (c i₀ k - g k)| := by ring_nf
        _ ≤ |c i₀ k| + |c i₀ k - g k| := abs_sub _ _
    linarith
  set G := goodSet f T P Q X c t₀ τ p₀ q₀ D δ with hGdef
  have hGc : lam Gᶜ = 0 := goodSet_compl lam f T P Q X c hgood
  -- lower bound from the floors
  set Tw := τ * D ^ 2 * V * δ ^ d with hTw
  have hTw0 : 0 < Tw := by positivity
  have hlow : ENNReal.ofReal (S.card * (Tw / A₀)) ≤ lam {ω | f ω ∈ S} := by
    have hU : {ω | f ω ∈ S} = ⋃ i ∈ S, {ω | f ω = i} := by ext ω; simp
    rw [hU, measure_biUnion_finset]
    · calc ENNReal.ofReal (S.card * (Tw / A₀)) = ∑ _i ∈ S, ENNReal.ofReal (Tw / A₀) := by
            rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
              ENNReal.ofReal_natCast]
        _ ≤ ∑ i ∈ S, lam {ω | f ω = i} := Finset.sum_le_sum fun i _ => hfloor i
    · intro i _ j _ hij
      exact Set.disjoint_left.mpr fun ω h1 h2 => hij (h1.symm.trans h2)
    · intro i _
      exact hf (measurableSet_singleton i)
  -- upper bound from the caps near the common graph `g`
  set ρ := δm / (4 * τ) + δm / (4 * D) with hρdef
  have hρ : ρ ≤ δ / (30720 * E) := rho_le hτ hD hδ hE1 hmτ hmD
  have hρ0 : 0 ≤ ρ := by positivity
  set θ := 15 * (1024 * E) * ρ with hθdef
  have hθ : θ ≤ δ / 2 := by
    have : 15 * (1024 * E) * ρ ≤ 15 * (1024 * E) * (δ / (30720 * E)) :=
      mul_le_mul_of_nonneg_left hρ (by positivity)
    have h2 : 15 * (1024 * E) * (δ / (30720 * E)) = δ / 2 := by field_simp; ring
    linarith
  have hθ0 : 0 ≤ θ := by positivity
  have hρ78 : ρ ≤ 7 / 8 := by
    have : δ / (30720 * E) ≤ 7 / 8 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hEm : 15360 * δm ≤ 15360 * E * δm := by
    have := mul_le_mul_of_nonneg_left hE1 (by positivity : (0 : ℝ) ≤ 15360 * δm)
    linarith
  have hmτ' : δm ≤ τ / 2 := by
    have := mul_le_mul_of_nonneg_right hδ1 hτ.le
    linarith
  have hmD' : δm ≤ D / 2 := by
    have := mul_le_mul_of_nonneg_right hδ1 hD.le
    linarith
  set σ := min (δ + 20 * M) 1 with hσdef
  have hσδ : δ ≤ σ := le_min (by linarith) hδ1
  have hσ1 : σ ≤ 1 := min_le_right _ _
  have hσ0 : 0 < σ := hδ.trans_le hσδ
  have key := rect_slab_cap lam (fun ω => ![T ω, P ω, Q ω]) X
    (fun y' => q3 g (normVec t₀ τ p₀ q₀ D (y' 0) (y' 1) (y' 2)) - (δ / 2 + 10 * M))
    ({ω | f ω ∈ S} ∩ G) (W := δ + 20 * M) (θ := θ) (L := V * σ ^ d)
    ![t₀ + τ / 2, p₀ + D / 2, q₀ + D / 2] ![τ / 2, D / 2, D / 2] hδm hσ0 hθ0 (by linarith)
    (by
      intro k
      fin_cases k
      · exact hmτ'
      · exact hmD'
      · exact hmD')
    (by positivity)
    (by
      intro z hz y' hy'
      obtain ⟨hzT, hzP, hzQ, -⟩ := hz.2
      rw [sub_sub_sub_cancel_right]
      exact offset_close hτ hD hg (fun k => abs_normVec_le hτ hD hzT hzP hzQ k) hy' hρ78)
    (by
      intro z hz
      obtain ⟨hfS, hzT, hzP, hzQ, hfit⟩ := hz
      have hfS' := (Finset.mem_filter.mp hfS).2
      set u := normVec t₀ τ p₀ q₀ D (T z) (P z) (Q z) with hudef
      have hu : ∀ k, |u k| ≤ 1 := fun k => (abs_normVec_le hτ hD hzT hzP hzQ k).trans (by norm_num)
      have hdiff : |q3 (c (f z)) u - q3 g u| ≤ 10 * M := by
        rw [← q3_sub]
        exact abs_q3_le (fun k => by simpa using hfS' k) hu
      have h1 := abs_le.mp hfit
      have h2 := abs_le.mp hdiff
      refine ⟨?_, ?_, ?_⟩
      · intro k
        fin_cases k
        · simp only [Fin.zero_eta, Matrix.cons_val_zero]
          rw [abs_le]; constructor <;> linarith [hzT.1, hzT.2]
        · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
          rw [abs_le]; constructor <;> linarith [hzP.1, hzP.2]
        · simp only [Fin.reduceFinMk, Matrix.cons_val]
          rw [abs_le]; constructor <;> linarith [hzQ.1, hzQ.2]
      · change q3 g u - (δ / 2 + 10 * M) ≤ X z
        linarith
      · change X z ≤ q3 g u - (δ / 2 + 10 * M) + (δ + 20 * M)
        linarith)
    (by
      intro cc j
      have := hcap σ hσδ hσ1 cc j
      simpa only [mul_assoc] using this)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at key
  rw [measure_inter_conull hGc] at key
  -- compare
  set Bnd := 343 * (τ / 2 * (D / 2) * (D / 2)) * ((δ + 20 * M + 2 * θ) / σ + 2) * (V * σ ^ d)
    with hBnd
  have hBnd0 : 0 ≤ Bnd := by
    have : 0 ≤ (δ + 20 * M + 2 * θ) / σ := div_nonneg (by linarith) hσ0.le
    have : 0 ≤ σ ^ d := Real.rpow_nonneg hσ0.le d
    positivity
  have hcard : S.card * (Tw / A₀) ≤ Bnd :=
    (ENNReal.ofReal_le_ofReal_iff hBnd0).mp (hlow.trans key)
  -- the bound in both regimes
  have hMd : 0 < M ^ d := Real.rpow_pos_of_pos hM0 d
  have hBndM : Bnd ≤ 1843968 * E * (τ * D ^ 2 * V) * M ^ d := by
    have hτD : 0 < τ * D ^ 2 * V := by positivity
    by_cases hW1 : δ + 20 * M ≤ 1
    · have hσW : σ = δ + 20 * M := min_eq_left hW1
      have hfac : (δ + 20 * M + 2 * θ) / σ + 2 ≤ 4 := by
        rw [hσW, div_add' _ _ _ (by linarith), div_le_iff₀ (by linarith)]; linarith
      have hσd : σ ^ d ≤ 21 * M ^ d := by
        rw [hσW]
        calc (δ + 20 * M) ^ d ≤ (21 * M) ^ d :=
              Real.rpow_le_rpow (by linarith) (by linarith) hd0
          _ = 21 ^ d * M ^ d := Real.mul_rpow (by norm_num) hM0.le
          _ ≤ 21 * M ^ d := by
              apply mul_le_mul_of_nonneg_right _ hMd.le
              calc (21 : ℝ) ^ d ≤ 21 ^ (1 : ℝ) :=
                    Real.rpow_le_rpow_of_exponent_le (by norm_num) hd1.le
                _ = 21 := Real.rpow_one 21
      calc Bnd ≤ 343 * (τ / 2 * (D / 2) * (D / 2)) * 4 * (V * (21 * M ^ d)) := by
            rw [hBnd]
            have : 0 ≤ (δ + 20 * M + 2 * θ) / σ + 2 := by
              have := div_nonneg (by linarith : (0 : ℝ) ≤ δ + 20 * M + 2 * θ) hσ0.le
              linarith
            gcongr
        _ = 3601.5 * (τ * D ^ 2 * V) * M ^ d := by ring
        _ ≤ 1843968 * E * (τ * D ^ 2 * V) * M ^ d := by
            have : (3601.5 : ℝ) ≤ 1843968 * E := by linarith
            gcongr
    · have hσ1' : σ = 1 := min_eq_right (by linarith)
      have hfac : (δ + 20 * M + 2 * θ) / σ + 2 ≤ 84 * M := by
        rw [hσ1', div_one]; push Not at hW1; linarith
      have hM1 : M ≤ 512 * E * M ^ d := by
        have hsplit : M = M ^ d * M ^ (1 - d) := by
          rw [← Real.rpow_add hM0, add_sub_cancel, Real.rpow_one]
        have h1 : M ^ (1 - d) ≤ (512 * E) ^ (1 - d) :=
          Real.rpow_le_rpow hM0.le hME (by linarith)
        have h2 : (512 * E) ^ (1 - d) ≤ 512 * E := by
          calc (512 * E) ^ (1 - d) ≤ (512 * E) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
            _ = 512 * E := Real.rpow_one _
        calc M = M ^ d * M ^ (1 - d) := hsplit
          _ ≤ M ^ d * (512 * E) := mul_le_mul_of_nonneg_left (h1.trans h2) hMd.le
          _ = 512 * E * M ^ d := by ring
      calc Bnd ≤ 343 * (τ / 2 * (D / 2) * (D / 2)) * (84 * M) * (V * 1) := by
            rw [hBnd, hσ1', Real.one_rpow]
            rw [hσ1'] at hfac
            gcongr
        _ = 3601.5 * (τ * D ^ 2 * V) * M := by ring
        _ ≤ 3601.5 * (τ * D ^ 2 * V) * (512 * E * M ^ d) := by gcongr
        _ = 1843968 * E * (τ * D ^ 2 * V) * M ^ d := by ring
  -- conclude
  have hδd : 0 < δ ^ d := Real.rpow_pos_of_pos hδ d
  have h1 : (S.card : ℝ) * Tw ≤ A₀ * (1843968 * E * (τ * D ^ 2 * V) * M ^ d) := by
    have := hcard.trans hBndM
    rw [mul_div_assoc'] at this
    rw [div_le_iff₀ hA₀] at this
    linarith
  have h2 : (S.card : ℝ) ≤ 1843968 * A₀ * E * (M ^ d / δ ^ d) := by
    have h3 : (S.card : ℝ) ≤ A₀ * (1843968 * E * (τ * D ^ 2 * V) * M ^ d) / Tw :=
      (le_div_iff₀ hTw0).mpr h1
    have h4 : A₀ * (1843968 * E * (τ * D ^ 2 * V) * M ^ d) / Tw =
        1843968 * A₀ * E * (M ^ d / δ ^ d) := by
      rw [hTw]; field_simp
    linarith
  rw [Real.div_rpow hM0.le hδ.le]
  have : 0 ≤ A₀ * E * (M ^ d / δ ^ d) := by positivity
  linarith

end Caps

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3
