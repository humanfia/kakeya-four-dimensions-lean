-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.MultiscaleCoreSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/MultiscaleCoreSource.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 83ada3e49b5540f6b00606ae3df6268df68021ab,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/MultiscaleCoreSource.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.BroadCoreSource

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native
open scoped ENNReal BigOperators

noncomputable section

/-- Original pure bands construct value entries and coherent cores at every
registered depth. One common original source retains all these cores, with
the sum of their original global deletion budgets. The branch exponents
are fixed before the problem, path, number of depths and source laws. -/
theorem exists_broad_multiscale_core_source (q : ℕ) (hq : 7 ≤ q) :
    ∃ e rad : ℕ, 4 ≤ e ∧ 1 ≤ rad ∧
    ∀ {T : Type*} {d : ProblemData}, d.Valid →
    ∀ {k : ℕ} {p : PathData (d.W k)}
      {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ},
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
        κ₁ m s δ₀ Mp Dp σ →
    ∀ {H₀ : Fin (d.W k) → Set Event} {u : T → ℝ} {τ ε : ℝ},
    ∀ Q : PreparedAngularPath d k p m H₀ u τ, Q.uniformPureBounds ε → 0 ≤ τ+ε →
      (∀ w, H₀ w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b}) →
    ∀ {i stop : ℕ} {mesh envelope r fraction : ℝ} {θ : ENNReal}
      {F : PaletteFamily Q i stop mesh envelope θ},
    ∀ broad : BroadResidual F r fraction,
    ∀ (n : ℕ) (depth : Fin n → ℕ),
      (∀ j, depth j < m) → (∀ j, 0 ≤ p.r (depth j)) → (∀ j, p.r (depth j) ≤ d.L) →
    ∀ qcore : ℕ,
    let K := nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ+ε)
    ∃ (H : Fin n → Fin (d.W k) → Set Event)
      (V : (j : Fin n) → ValueBranchData d k p (H j) (depth j) K q e rad)
      (cores : (j : Fin n) → (V j).CoreFamilies (ENNReal.ofReal ((K^qcore)⁻¹)))
      (current : Fin (d.W k) → Set Event),
      (∀ j w, MeasurableSet (H j w) ∧ H j w⊆broad.residual w ∧
        ((d.ν k w).prod volume).restrict (H j w)=
          ((d.ν k w).prod volume).restrict (broad.residual w)) ∧
      (∀ w, MeasurableSet (current w) ∧ current w⊆broad.residual w) ∧
      (∀ j w, current w⊆(V j).coreRetained (cores j) w) ∧
      (∑ w, ENNReal.ofReal (d.ω k w)*
        ((d.ν k w).prod volume) (broad.residual w\current w)) ≤
        (n:ENNReal)*(ENNReal.ofReal (K^10)*ENNReal.ofReal ((K^q)⁻¹)+
          ENNReal.ofReal (K^10)*ENNReal.ofReal (2*K^(3*rad+18))*
            ENNReal.ofReal ((K^qcore)⁻¹)) := by
  classical
  obtain ⟨e,rad,he,hrad,hfactory⟩ := exists_broad_value_branch_data q hq
  refine ⟨e,rad,he,hrad,?_⟩
  intro T d hd k p κ₁ m s δ₀ Mp Dp σ hp H₀ u τ ε Q hpure htol hHterminal
    i stop mesh envelope r fraction θ F broad n depth hdepth hr hrL qcore
  let K := nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ+ε)
  have hN : 1 ≤ d.N k := by linarith [hd.1 k]
  obtain ⟨hK,hκK,_,_⟩ := native_pre_geometry_envelope_bounds hp.1 hN htol
  have hK2 : 2 ≤ K := by dsimp only [K]; linarith
  have hvalues (j : Fin n) := hfactory hd hp Q hpure htol hHterminal broad
    (depth j) (hdepth j) (hr j) (hrL j)
  choose H hHm hHs hHeq hV using hvalues
  let V (j : Fin n) := Classical.choice (hV j)
  let cores (j : Fin n) := Classical.choice ((V j).exists_core_families hd hp hK2 hκK
    (ENNReal.ofReal ((K^qcore)⁻¹)))
  have hcoreBudget (j : Fin n) := (V j).core_retention_budget hd hp (cores j)
  let current := fun w => broad.residual w∩⋂ j, (V j).coreRetained (cores j) w
  have hcurrent (w) : MeasurableSet (current w) :=
    (broad.measurable w).inter (MeasurableSet.iInter (fun j => ((hcoreBudget j).1 w).1))
  have hcurrentSub (w) : current w⊆broad.residual w := inter_subset_left
  have hcurrentCore (j : Fin n) (w) : current w⊆(V j).coreRetained (cores j) w :=
    fun z hz => mem_iInter.mp hz.2 j
  let cost := ENNReal.ofReal (K^10)*ENNReal.ofReal ((K^q)⁻¹)+
    ENNReal.ofReal (K^10)*ENNReal.ofReal (2*K^(3*rad+18))*ENNReal.ofReal ((K^qcore)⁻¹)
  have hlocal (j : Fin n) : (∑ w, ENNReal.ofReal (d.ω k w)*
      ((d.ν k w).prod volume) (broad.residual w\(V j).coreRetained (cores j) w)) ≤ cost := by
    have hsame (w) : ((d.ν k w).prod volume) (broad.residual w\(V j).coreRetained (cores j) w)=
        ((d.ν k w).prod volume) (H j w\(V j).coreRetained (cores j) w) := by
      have hh := congrArg (fun μ : Measure Event => μ ((V j).coreRetained (cores j) w)ᶜ) (hHeq j w)
      simpa only [Measure.restrict_apply (((hcoreBudget j).1 w).1.compl),Set.sdiff_eq,inter_comm] using hh.symm
    have hsplit (w) : H j w\(V j).coreRetained (cores j) w ⊆
        (H j w\(V j).residual w)∪((V j).residual w\(V j).coreRetained (cores j) w) := by
      intro z hz
      by_cases hv : z∈(V j).residual w
      · exact Or.inr ⟨hv,hz.2⟩
      · exact Or.inl ⟨hz.1,hv⟩
    calc
      _ = ∑ w, ENNReal.ofReal (d.ω k w)*
          ((d.ν k w).prod volume) (H j w\(V j).coreRetained (cores j) w) := by
        simp_rw [hsame]
      _ ≤ ∑ w, ENNReal.ofReal (d.ω k w)*
          (((d.ν k w).prod volume) (H j w\(V j).residual w)+
            ((d.ν k w).prod volume) ((V j).residual w\(V j).coreRetained (cores j) w)) :=
        Finset.sum_le_sum (fun w _ => mul_le_mul' le_rfl
          ((measure_mono (hsplit w)).trans (measure_union_le _ _)))
      _ = (∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (H j w\(V j).residual w))+
          ∑ w, ENNReal.ofReal (d.ω k w)*
            ((d.ν k w).prod volume) ((V j).residual w\(V j).coreRetained (cores j) w) := by
        simp only [mul_add,Finset.sum_add_distrib]
      _ ≤ cost := add_le_add (V j).loss (hcoreBudget j).2
  have hdiscard (w) : broad.residual w\current w⊆
      ⋃ j, broad.residual w\(V j).coreRetained (cores j) w := by
    intro z hz
    by_contra h
    apply hz.2
    refine ⟨hz.1,mem_iInter.mpr ?_⟩
    intro j
    by_contra hj
    exact h (mem_iUnion.mpr ⟨j,hz.1,hj⟩)
  refine ⟨H,V,cores,current,(fun j w => ⟨hHm j w,hHs j w,hHeq j w⟩),
    (fun w => ⟨hcurrent w,hcurrentSub w⟩),hcurrentCore,?_⟩
  calc
    _ ≤ ∑ w, ENNReal.ofReal (d.ω k w)*
        (∑ j, ((d.ν k w).prod volume) (broad.residual w\(V j).coreRetained (cores j) w)) :=
      Finset.sum_le_sum (fun w _ => mul_le_mul' le_rfl
        ((measure_mono (hdiscard w)).trans (measure_iUnion_fintype_le _ _)))
    _ = ∑ j : Fin n, ∑ w, ENNReal.ofReal (d.ω k w)*
        ((d.ν k w).prod volume) (broad.residual w\(V j).coreRetained (cores j) w) := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ ∑ j : Fin n, cost := Finset.sum_le_sum (fun j _ => hlocal j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,cost,K]

/-- A fixed finite depth grid costs only one further native envelope power. -/
theorem multiscale_core_loss_small {K κ : ℝ} (n : ℕ)
    (hκ : 1 ≤ κ) (hK : 2304 ≤ K) (hκK : 3*κ ≤ K) (hn : (n:ℝ) ≤ K) :
    (n:ENNReal)*ENNReal.ofReal ((K^20)⁻¹) ≤ ENNReal.ofReal (κ⁻¹/64) := by
  have hκp : 0 < κ := zero_lt_one.trans_le hκ
  have hK1 : 1 ≤ K := by linarith
  have hKp : 0 < K := by linarith
  have hκK' : κ ≤ K := by linarith
  have h18 : (64:ℝ) ≤ K^18 :=
    (show (64:ℝ) ≤ K by linarith).trans (by
      simpa only [pow_one] using pow_le_pow_right₀ hK1 (by norm_num : (1:ℕ) ≤ 18))
  have hprod : (n:ℝ)*(64*κ) ≤ K^20 := by
    calc
      _ ≤ K*(64*K) := mul_le_mul hn (by linarith) (by positivity) hKp.le
      _ = 64*K^2 := by ring
      _ ≤ K^18*K^2 := mul_le_mul_of_nonneg_right h18 (sq_nonneg K)
      _ = _ := by rw [←pow_add]
  have hreal : (n:ℝ)*(K^20)⁻¹ ≤ κ⁻¹/64 := by
    have hh : (n:ℝ)/K^20 ≤ 1/(64*κ) :=
      (div_le_div_iff₀ (pow_pos hKp 20) (by positivity : 0 < 64*κ)).mpr (by simpa using hprod)
    simpa only [div_eq_mul_inv,mul_inv_rev,one_mul] using hh
  calc
    _ = ENNReal.ofReal ((n:ℝ)*(K^20)⁻¹) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg n),ENNReal.ofReal_natCast]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

/-- All registered original value/core families and a common source of
fixed original mass, without any per-depth mass hypothesis. -/
structure BroadMultiscaleCoreSource (d : ProblemData) (k : ℕ) (p : PathData (d.W k))
    (original : Fin (d.W k) → Set Event) (n : ℕ) (depth : Fin n → ℕ)
    (K : ℝ) (e R : ℕ) where
  source : Fin n → Fin (d.W k) → Set Event
  measurable : ∀ j w, MeasurableSet (source j w)
  subset : ∀ j w, source j w⊆original w
  original_law : ∀ j w, ((d.ν k w).prod volume).restrict (source j w)=
    ((d.ν k w).prod volume).restrict (original w)
  values : (j : Fin n) → ValueBranchData d k p (source j) (depth j) K 40 e R
  cores : (j : Fin n) → (values j).CoreFamilies (ENNReal.ofReal ((K^(3*R+58))⁻¹))
  current : Fin (d.W k) → Set Event
  current_measurable : ∀ w, MeasurableSet (current w)
  current_subset : ∀ w, current w⊆original w
  current_cores : ∀ j w, current w⊆(values j).coreRetained (cores j) w
  original_mass : ENNReal.ofReal (p.κ⁻¹/64) ≤
    ∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (current w)

/-- Fixed branch exponents construct a common original core source with
fixed original mass at every prescribed finite family of valid depths. -/
theorem exists_broad_multiscale_core_source_with_mass :
    ∃ e rad : ℕ, 4 ≤ e ∧ 1 ≤ rad ∧
    ∀ {T : Type*} {d : ProblemData}, d.Valid →
    ∀ {k : ℕ} {p : PathData (d.W k)}
      {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ} {Mp Dp : ℕ} {σ : ℝ},
      p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
        κ₁ m s δ₀ Mp Dp σ →
    ∀ {H₀ : Fin (d.W k) → Set Event} {u : T → ℝ} {τ ε : ℝ},
    ∀ Q : PreparedAngularPath d k p m H₀ u τ, Q.uniformPureBounds ε → 0 ≤ τ+ε →
      (∀ w, H₀ w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b}) →
    ∀ {i stop : ℕ} {mesh envelope r fraction : ℝ} {θ : ENNReal}
      {F : PaletteFamily Q i stop mesh envelope θ},
    ∀ broad : BroadResidual F r fraction,
    ∀ (n : ℕ) (depth : Fin n → ℕ),
      (∀ j, depth j < m) → (∀ j, 0 ≤ p.r (depth j)) → (∀ j, p.r (depth j) ≤ d.L) →
      (n:ℝ) ≤ nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ+ε) →
      Nonempty (BroadMultiscaleCoreSource d k p broad.residual n depth
        (nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ+ε)) e rad) := by
  classical
  obtain ⟨e,rad,he,hrad,hfactory⟩ := exists_broad_multiscale_core_source 40 (by norm_num)
  refine ⟨e,rad,he,hrad,?_⟩
  intro T d hd k p κ₁ m s δ₀ Mp Dp σ hp H₀ u τ ε Q hpure htol hHterminal
    i stop mesh envelope r fraction θ F broad n depth hdepth hr hrL hn
  let K := nativePreGeometryEnvelope p.κ (d.K k) (d.N k) (τ+ε)
  have hN : 1 ≤ d.N k := by linarith [hd.1 k]
  obtain ⟨hK,hκK,_,_⟩ := native_pre_geometry_envelope_bounds hp.1 hN htol
  have hκp : 0 < p.κ := zero_lt_one.trans_le hp.1
  obtain ⟨H,V,cores,current,hH,hcurrent,hcore,hloss⟩ := hfactory hd hp Q hpure htol hHterminal
    broad n depth hdepth hr hrL (3*rad+58)
  let cost := (n:ENNReal)*(ENNReal.ofReal (K^10)*ENNReal.ofReal ((K^40)⁻¹)+
    ENNReal.ofReal (K^10)*ENNReal.ofReal (2*K^(3*rad+18))*ENNReal.ofReal ((K^(3*rad+58))⁻¹))
  have hbudget : (∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (broad.residual w)) ≤
      (∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (current w))+cost := by
    calc
      _ ≤ ∑ w, ENNReal.ofReal (d.ω k w)*
          (((d.ν k w).prod volume) (current w)+
            ((d.ν k w).prod volume) (broad.residual w\current w)) := by
        apply Finset.sum_le_sum
        intro w _
        apply mul_le_mul' le_rfl
        apply (measure_mono (show broad.residual w⊆current w∪(broad.residual w\current w) from fun z hz => by
          by_cases h : z∈current w
          · exact Or.inl h
          · exact Or.inr ⟨hz,h⟩)).trans
        exact measure_union_le _ _
      _ = (∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (current w))+
          ∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (broad.residual w\current w) := by
        simp only [mul_add,Finset.sum_add_distrib]
      _ ≤ _ := add_le_add le_rfl hloss
  have hcost : cost ≤ ENNReal.ofReal (p.κ⁻¹/64) := by
    apply (mul_le_mul' le_rfl (original_value_core_loss_bound (by linarith : 2 ≤ K) rad)).trans
    exact multiscale_core_loss_small n hp.1 hK hκK hn
  have hdouble : ENNReal.ofReal (p.κ⁻¹/64)+ENNReal.ofReal (p.κ⁻¹/64) ≤
      ∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (broad.residual w) := by
    rw [←ENNReal.ofReal_add (by positivity) (by positivity)]
    convert broad.mass using 1
    congr 1
    ring
  refine ⟨{
    source := H
    measurable := fun j w => (hH j w).1
    subset := fun j w => (hH j w).2.1
    original_law := fun j w => (hH j w).2.2
    values := V
    cores := cores
    current := current
    current_measurable := fun w => (hcurrent w).1
    current_subset := fun w => (hcurrent w).2
    current_cores := hcore
    original_mass := Submission.Obl.k4_scalar_grid_cartesian_field.pruning_mass_floor
      ENNReal.ofReal_ne_top hdouble hbudget hcost }⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
