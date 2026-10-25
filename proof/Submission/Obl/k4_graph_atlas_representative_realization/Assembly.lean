import Submission.Obl.k4_graph_atlas_representative_realization.Chart

namespace Submission.Obl.k4_graph_atlas_representative_realization

open Submission.Obl.k4_quadratic_atlas_normalization

theorem realization : ∀M:ℕ,∃M':ℕ,M≤ M'∧∀L θ gain ζ:ℝ,0 < L→ 0 < θ→ θ≤1/4→ 0 < gain→ gain≤1/8→ 0 < ζ→ ζ≤1→ ∃N₀:ℝ,2≤ N₀∧∀Nk:ℝ,N₀≤ Nk→ ∀(W:ℕ) (ω:Fin W→ ℝ) (ν:Fin W→ MeasureTheory.Measure (ℕ×(Fin 6→ ℝ))) (E:Fin W→ Set ((ℕ×(Fin 6→ ℝ))×ℝ)) (B:Fin W→ ℝ) (r₀ h β:ℝ) (D T C:ℕ) (γ:Fin C→ Fin W) (j:Fin C→ Fin (2^T)) (c u:Fin C→ EuclideanSpace ℝ (Fin 2)) (Q:Fin C→ Matrix (Fin 2) (Fin 2) ℝ) (P:Fin C→ MvPolynomial (Fin 4) ℝ) (sc:Fin C→ ℝ) (A:Fin C→ Set (ℕ×(Fin 6→ ℝ))) (F:Fin C→ Set ((ℕ×(Fin 6→ ℝ))×ℝ)) (lst:Fin W→ (EuclideanSpace ℝ (Fin 3)×ℤ)→ Finset (Fin C)),0≤ r₀→ gain≤ h→ h≤1/8→ r₀+2*h*L≤ L→ 0 < β→ β≤ζ/4→ ((C:ℝ)≤ Nk^M∧(∀w,0 < B w∧B w≤ Nk^M∧(B w)⁻¹≤ Nk^M)∧(∀b b',b≠b'→ γ b=γ b'→ j b=j b'→ Disjoint (A b) (A b'))∧(∀w o,((lst w o).card:ℝ)≤ Nk^β)∧(∀w b,MeasurableSet {o | b∈lst w o})∧(∀b,Matrix.det (Q b)≠0∧‖c b‖+‖u b‖≤ Nk^M∧(∑e:Fin 2,∑e':Fin 2,(|Q b e e'|+|(Q b)⁻¹ e e'|))≤ Nk^M∧(∑e:Fin 2,∑e':Fin 2,|Q b e e'|)≤ Nk^β/(2:ℝ)^T∧(P b).totalDegree≤2∧(∀e,|(P b).coeff e|≤ Nk^M)∧0 < sc b∧sc b≤ Nk^M∧(sc b)⁻¹≤ Nk^M∧MeasurableSet (A b)∧MeasurableSet (F b)∧(∀i,fmt 6 (Nk^M) D {z | (i,z)∈A b}∧fmt 7 (Nk^M) D {z:Fin 7→ ℝ | ((i,fun a:Fin 6=> z a.castSucc),z 6)∈F b})∧(∀l∈A b,(l.1:ℝ)≤ Nk^M∧(∀e,|l.2 e|≤ Nk^M)∧∀t∈Set.Icc ((j b:ℕ)/(2:ℝ)^T) (((j b:ℕ)+1)/(2:ℝ)^T),‖Matrix.toEuclideanLin (Q b)⁻¹ (y l t - c b - t•u b)‖≤ Nk^β)∧(∀p∈F b,p∈E (γ b)∧p.1∈A b∧p.2∈Set.Icc ((j b:ℕ)/(2:ℝ)^T) (((j b:ℕ)+1)/(2:ℝ)^T))∧(∀l∈A b,∀t∈Set.Icc ((j b:ℕ)/(2:ℝ)^T) (((j b:ℕ)+1)/(2:ℝ)^T),∃w₀:ℝ,|(x l t) 3 - w₀|≤δ Nk r₀/B (γ b)*Nk^(-(θ*h*L))∧MvPolynomial.eval (Function.update (x l t) (3:Fin 4) w₀) (P b)=0∧sc b/2≤|MvPolynomial.eval (Function.update (x l t) (3:Fin 4) w₀) (MvPolynomial.pderiv (3:Fin 4) (P b))|∧|MvPolynomial.eval (Function.update (x l t) (3:Fin 4) w₀) (MvPolynomial.pderiv (3:Fin 4) (P b))|≤2*sc b))∧ENNReal.ofReal (Nk^(-β))≤∑b,ENNReal.ofReal (ω (γ b))*((ν (γ b)).prod MeasureTheory.volume) {p | p∈F b∧b∈lst (γ b) (obs (B (γ b)) (δ Nk L) p)})→ ∃(r₂:ℝ) (C₂:ℕ) (γ₂:Fin C₂→ Fin W) (j₂:Fin C₂→ Fin (2^T)) (c₂ u₂:Fin C₂→ EuclideanSpace ℝ (Fin 2)) (Q₂:Fin C₂→ Matrix (Fin 2) (Fin 2) ℝ) (R₂:Fin C₂→ MvPolynomial (Fin 4) ℝ) (A₂:Fin C₂→ Set (ℕ×(Fin 6→ ℝ))) (F₂:Fin C₂→ Set ((ℕ×(Fin 6→ ℝ))×ℝ)) (lst₂:Fin W→ (EuclideanSpace ℝ (Fin 3)×ℤ)→ Finset (Fin C₂)),r₀+(θ/4)*gain*L≤ r₂∧r₂+(θ/4)*gain*L≤ L∧(((C₂):ℝ)≤ Nk^(M')∧(∀b b',b≠b'→ (γ₂) b=(γ₂) b'→ (j₂) b=(j₂) b'→ Disjoint ((A₂) b) ((A₂) b'))∧(∀w o,(((lst₂) w o).card:ℝ)≤ Nk^ζ)∧(∀w b,MeasurableSet {o | b∈(lst₂) w o})∧(∀b,chart Nk (M') D (Nk^ζ) T (((j₂) b:ℕ):ℝ) r₂ (B ((γ₂) b)) (E ((γ₂) b)) ((c₂) b) ((u₂) b) ((Q₂) b) ((R₂) b) ((A₂) b) ((F₂) b) True)∧ENNReal.ofReal (Nk^(-ζ))≤∑b,ENNReal.ofReal (ω ((γ₂) b))*((ν ((γ₂) b)).prod MeasureTheory.volume) {p | p∈(F₂) b∧b∈(lst₂) ((γ₂) b) (obs (B ((γ₂) b)) (δ Nk L) p)}) := by
  intro M
  refine ⟨3 * M + 2, by omega, ?_⟩
  intro L θ gain ζ hL hθ hθmax hgain hgainmax hζ hζmax
  obtain ⟨N₀, hN₀, hthreshold⟩ := exists_threshold
    (show 0 < (θ / 4) * gain * L by positivity) hζ
  refine ⟨N₀, hN₀, ?_⟩
  intro Nk hNk W ω ν E B r₀ h β D T C γ j c u Q P sc A F lst
    hr₀ hh hhmax hrL hβ hβζ hin
  obtain ⟨hC, hB, hdisjoint, hlst, hmeas, hcharts, hmass⟩ := hin
  have hN2 : 2 ≤ Nk := hN₀.trans hNk
  have hN1 : 1 ≤ Nk := by linarith
  have hNpos : 0 < Nk := by linarith
  have hM : M ≤ 3 * M + 2 := by omega
  have hpow : Nk ^ M ≤ Nk ^ (3 * M + 2) := pow_le_pow_right₀ hN1 hM
  have hβζ' : β ≤ ζ := by linarith
  have hκ : Nk ^ β ≤ Nk ^ ζ := Real.rpow_le_rpow_of_exponent_le hN1 hβζ'
  obtain ⟨hNa, hNζ⟩ := hthreshold Nk hNk
  let r₂ := r₀ + (θ / 4) * gain * L
  have hr₂ : 0 ≤ r₂ := by dsimp [r₂]; positivity
  have hstep : (θ / 4) * gain ≤ h := by
    have : (θ / 4) * gain ≤ gain :=
      mul_le_of_le_one_left hgain.le (by linarith)
    exact this.trans hh
  have hdepth : r₂ + (θ / 4) * gain * L ≤ L := by
    have hm := mul_le_mul_of_nonneg_right hstep hL.le
    dsimp [r₂]
    nlinarith
  have hcoef : 2 * (Nk ^ M) ^ 3 ≤ Nk ^ (3 * M + 2) := by
    have hsquare : 2 ≤ Nk ^ 2 := by nlinarith
    rw [← pow_mul, Nat.mul_comm M 3]
    calc
      _ ≤ Nk ^ 2 * Nk ^ (3 * M) :=
        mul_le_mul_of_nonneg_right hsquare (by positivity)
      _ = _ := by rw [pow_add]; ring
  refine ⟨r₂, C, γ, j, c, u, Q,
    (fun b => normalizedTest (P b) (sc b) (B (γ b)) (δ Nk r₂)),
    A, F, lst, le_rfl, hdepth, hC.trans hpow, hdisjoint,
    (fun w o => (hlst w o).trans hκ), hmeas, ?_, ?_⟩
  · intro b
    exact realize_chart hN2 hM hκ hNζ (hB (γ b)).1 (hB (γ b)).2.1 hr₂ hcoef
      (root_error_compare hN1 hL hθ hgain hh (hB (γ b)).1 hNa) (hcharts b)
  · exact (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : -ζ ≤ -β))).trans hmass

end Submission.Obl.k4_graph_atlas_representative_realization
