import Submission.Obl.k4_scalar_chart_normalization.Defs
import Submission.Obl.k4_scalar_chart_normalization.AngularTransfer
import Submission.Obl.k4_scalar_grid_density_extension.GridSlices
import Submission.Obl.k4_scalar_grid_density_extension.GridTypical

namespace Submission.Obl.k4_scalar_chart_normalization

open MeasureTheory Set Filter
open scoped ENNReal Topology
open Submission.Obl.k4_scalar_grid_density_extension

/-- Each original incidence law has mass at most one. -/
theorem mu_univ_le_one {p : Problem} (hp : Exact p) (k : ℕ) (a : Fin (p.1 k)) :
    mu p k a univ ≤ 1 := by
  have hw := hp.2.1 k
  have ha := hw.2.2.2.1 a
  have : IsProbabilityMeasure (p.nu k a) := ha.1
  calc
    mu p k a univ = (p.nu k a).prod volume (p.E k a) := by simp only [mu, Measure.restrict_apply_univ]
    _ ≤ (p.nu k a).prod volume (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono ha.2.2.2.2.1
    _ = 1 := by simp [Measure.prod_prod, Real.volume_Icc]

/-- A canonical representative of the coarse bin containing the left endpoint
of a given fine bin. -/
noncomputable def coarseBinStart (N r L : ℝ) (b : ℤ) : ℤ :=
  ⌊(b : ℝ) * (N ^ (-L)) / (N ^ (-r))⌋

/-- The extra bit recording which of the two overlapping coarse bins occurs. -/
noncomputable def coarseFlag (N r L : ℝ) (p : Incidence) : Fin 2 :=
  if hiddenLabel N r p = coarseBinStart N r L (hiddenLabel N L p) then 0 else 1

noncomputable def coarseMap (N r L : ℝ) (i : Fin 2) (z : ObsSpace) : ObsSpace :=
  (z.1, coarseBinStart N r L z.2 + (i : ℕ))

theorem measurable_coarseMap (N r L : ℝ) (i : Fin 2) : Measurable (coarseMap N r L i) :=
  measurable_fst.prodMk ((measurable_of_countable
    (fun b : ℤ => coarseBinStart N r L b + (i : ℕ))).comp measurable_snd)

theorem measurable_coarseFlag (N r L : ℝ) : Measurable (coarseFlag N r L) := by
  apply Measurable.ite
  · exact measurableSet_eq_fun (measurable_hiddenLabel N r)
      ((measurable_of_countable (coarseBinStart N r L)).comp (measurable_hiddenLabel N L))
  · exact measurable_const
  · exact measurable_const

theorem coarseMap_flag {N r L : ℝ} (hN : 1 ≤ N) (hrL : r ≤ L) (p : Incidence) :
    coarseMap N r L (coarseFlag N r L p) (obs N L p) = obs N r p := by
  have H := floorCompatible_coarse_mem (width_pos hN L) (width_anti hN hrL)
    (hiddenLabel N L p) (hiddenLabel N r p) (hidden_compatible N r L p)
  simp only [Finset.mem_insert, Finset.mem_singleton] at H
  dsimp [coarseMap, coarseFlag]
  split_ifs with h
  · simp only [Fin.val_zero, Nat.cast_zero, add_zero]
    exact Prod.ext rfl h.symm
  · rcases H with H | H
    · exact (h H).elim
    · simp only [Fin.val_one, Nat.cast_one]
      exact Prod.ext rfl H.symm

/-- Canonical joint densities at a coarsened terminal depth. -/
noncomputable def coarseDensity (p : Problem) (r : ℝ) (k : ℕ) (a : Fin (p.1 k))
    (u : ℝ) : JointSpace → ENNReal :=
  ((mu p k a).map (aug (p.N k) r u)).rnDeriv jointReference

theorem coarseDensity_law {p : Problem} (hp : Exact p) {r : ℝ}
    (hr : 0 ≤ r) (hrL : r ≤ p.L) (k : ℕ) (a : Fin (p.1 k)) (u : ℝ) :
    Measurable (coarseDensity p r k a u) ∧
      (mu p k a).map (aug (p.N k) r u) = jointReference.withDensity (coarseDensity p r k a u) := by
  have : IsFiniteMeasure (mu p k a) := ⟨(mu_univ_le_one hp k a).trans_lt (by simp)⟩
  obtain ⟨hm, he⟩ := hp.2.2.1 k a r hr hrL
  have habs : (mu p k a).map (obs (p.N k) r) ≪ reference := by
    change (mu p k a).map (obs (p.N k) r) = reference.withDensity (p.rho k a r) at he
    rw [he]
    exact withDensity_absolutelyContinuous _ _
  have H := append_discrete_absolutelyContinuous (mu p k a) reference
    (obs (p.N k) r) (measurable_obs_label _ _) (velocityLabel (p.N k) u)
    (measurable_velocityLabel _ _) habs
  exact ⟨Measure.measurable_rnDeriv _ _, (Measure.withDensity_rnDeriv_eq _ _ H).symm⟩

/-- The quantitative one-world coarsening estimate. -/
theorem coarse_angular_estimate {p : Problem} (hp : Exact p) {r u : ℝ}
    (hr : 0 ≤ r) (hrL : r ≤ p.L) (hu : 0 < u) (huU : u ≤ p.U)
    (k : ℕ) (a : Fin (p.1 k)) (c δ : ENNReal) (hδ : δ ≠ 0) (hδtop : δ ≠ ⊤) :
    (mu p k a) {z | 2 * (c / δ) * p.rho k a r (obs (p.N k) r z) <
      coarseDensity p r k a u (aug (p.N k) r u z)} ≤
      2 * ((mu p k a) {z | c * p.rho k a p.L (obs (p.N k) p.L z) <
        p.rhoA k a u (aug (p.N k) p.L u z)} + δ * 2 * (mu p k a) univ) := by
  classical
  let ν := mu p k a
  have : IsFiniteMeasure ν := ⟨(mu_univ_le_one hp k a).trans_lt (by simp)⟩
  obtain ⟨hf, hfmap⟩ := hp.2.2.1 k a p.L hp.1.2.2.2.2.2.1.le le_rfl
  obtain ⟨hF, hFmap⟩ := hp.2.2.2.1 k a u hu huU
  obtain ⟨hf', hfmap'⟩ := hp.2.2.1 k a r hr hrL
  obtain ⟨hF', hFmap'⟩ := coarseDensity_law hp hr hrL k a u
  have hg : ∀ i : Fin 2, ∃ g : ObsSpace → ENNReal, Measurable g ∧
      (ν.restrict (coarseFlag (p.N k) r p.L ⁻¹' {i})).map (obs (p.N k) p.L) =
        reference.withDensity g := by
    intro i
    exact Submission.Obl.k4_crop_angular_finite_tail.exists_density_of_le reference
      (Measure.restrict_le_self) (measurable_obs_label _ _) hfmap
  choose g hg hglaw using hg
  simpa only [Fintype.card_fin, Nat.cast_ofNat] using finite_label_angular_coarsening ν
    reference reference (Measure.count : Measure ℤ)
    (obs (p.N k) p.L) (measurable_obs_label _ _) (obs (p.N k) r) (measurable_obs_label _ _)
    (velocityLabel (p.N k) u) (measurable_velocityLabel _ _)
    (coarseFlag (p.N k) r p.L) (measurable_coarseFlag _ _ _)
    (coarseMap (p.N k) r p.L) (measurable_coarseMap _ _ _)
    (coarseMap_flag (by linarith [hp.1.1 k]) hrL)
    (p.rho k a p.L) (p.rhoA k a u) (p.rho k a r) (coarseDensity p r k a u)
    hf hF hf' hF' hfmap hFmap hfmap' hFmap' g hg hglaw c δ hδ hδtop


/-- The two sources of original exceptional mass used in angular coarsening. -/
noncomputable def pureBadMass (p : Problem) (r τ : ℝ) (k : ℕ) : ENNReal :=
  ∑ a, ENNReal.ofReal (p.w k a) * (mu p k a)
    {z | p.rho k a r (obs (p.N k) r z) < ENNReal.ofReal (p.N k ^ (-p.f r - τ)) ∨
      ENNReal.ofReal (p.N k ^ (-p.f r + τ)) < p.rho k a r (obs (p.N k) r z)}

noncomputable def angularBadMass (p : Problem) (u τ : ℝ) (k : ℕ) : ENNReal :=
  ∑ a, ENNReal.ofReal (p.w k a) * (mu p k a)
    {z | ENNReal.ofReal (p.N k ^ (-p.f p.L - p.S * u + τ)) <
      p.rhoA k a u (aug (p.N k) p.L u z)}

open Submission.Obl.k4_native_grid_profile_extension.Profiles

/-- Weighted incidence mass is at most one because the original mixture is a
probability mixture of restrictions of product priors. -/
theorem weighted_mu_univ_le_one {p : Problem} (hp : Exact p) (k : ℕ) :
    ∑ a, ENNReal.ofReal (p.w k a) * (mu p k a) univ ≤ 1 := by
  calc
    _ ≤ ∑ a, ENNReal.ofReal (p.w k a) * 1 := Finset.sum_le_sum fun a _ =>
      mul_le_mul' le_rfl (mu_univ_le_one hp k a)
    _ = ENNReal.ofReal (∑ a, p.w k a) := by
      simp only [mul_one]
      rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => (hp.2.1 k).2.1 a)]
    _ = 1 := by rw [(hp.2.1 k).2.2.1, ENNReal.ofReal_one]

private theorem angular_power_budget {N : ℝ} (hN : 1 ≤ N)
    (f σ u ε : ℝ) (h2 : 2 ≤ N ^ (4 * ε)) :
    2 * (ENNReal.ofReal (N ^ (-σ * u + 2 * ε)) / ENNReal.ofReal (N ^ (-ε))) *
        ENNReal.ofReal (N ^ (-f + ε)) ≤ ENNReal.ofReal (N ^ (-f - σ * u + 8 * ε)) := by
  have hNp : 0 < N := by linarith
  have hp : 0 < N ^ (-ε) := Real.rpow_pos_of_pos hNp _
  calc
    _ = ENNReal.ofReal (2 * (N ^ (-σ * u + 2 * ε) / N ^ (-ε)) * N ^ (-f + ε)) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
        ENNReal.ofReal_div_of_pos hp]
      norm_num
    _ = ENNReal.ofReal (2 * N ^ (-f - σ * u + 4 * ε)) := by
      congr 1
      rw [← Real.rpow_sub hNp]
      calc
        _ = 2 * (N ^ ((-σ * u + 2 * ε) - -ε) * N ^ (-f + ε)) := by ring
        _ = _ := by rw [← Real.rpow_add hNp]; congr 2; ring
    _ ≤ ENNReal.ofReal (N ^ (4 * ε) * N ^ (-f - σ * u + 4 * ε)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right h2 (by positivity))
    _ = _ := by rw [← Real.rpow_add hNp]; congr 2; ring

/-- A per-world estimate, expressed only in the original typical-density and
angular exceptional sets. -/
theorem coarse_angular_world_bound {p : Problem} (hp : Exact p) {r u ε : ℝ}
    (hr : 0 ≤ r) (hrL : r ≤ p.L) (hu : 0 < u) (huU : u ≤ p.U)
    (k : ℕ) (a : Fin (p.1 k)) (_hε : 0 < ε) (h2 : 2 ≤ p.N k ^ (4 * ε)) :
    (mu p k a) {z | ENNReal.ofReal (p.N k ^ (-p.f r - p.S * u + 8 * ε)) <
      coarseDensity p r k a u (aug (p.N k) r u z)} ≤
    (mu p k a) {z | p.rho k a r (obs (p.N k) r z) <
        ENNReal.ofReal (p.N k ^ (-p.f r - ε)) ∨
      ENNReal.ofReal (p.N k ^ (-p.f r + ε)) < p.rho k a r (obs (p.N k) r z)} +
      2 * ((mu p k a) {z | p.rho k a p.L (obs (p.N k) p.L z) <
          ENNReal.ofReal (p.N k ^ (-p.f p.L - ε)) ∨
        ENNReal.ofReal (p.N k ^ (-p.f p.L + ε)) < p.rho k a p.L (obs (p.N k) p.L z)} +
        (mu p k a) {z | ENNReal.ofReal (p.N k ^ (-p.f p.L - p.S * u + ε)) <
          p.rhoA k a u (aug (p.N k) p.L u z)} +
        ENNReal.ofReal (p.N k ^ (-ε)) * 2 * (mu p k a) univ) := by
  have hN : 1 ≤ p.N k := by linarith [hp.1.1 k]
  have hNp : 0 < p.N k := by linarith
  let c := ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * ε))
  let δ := ENNReal.ofReal (p.N k ^ (-ε))
  have hδ : δ ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hNp _)).ne'
  have H := coarse_angular_estimate hp hr hrL hu huU k a c δ hδ ENNReal.ofReal_ne_top
  let Bad (s : ℝ) : Set Incidence := {z | p.rho k a s (obs (p.N k) s z) <
      ENNReal.ofReal (p.N k ^ (-p.f s - ε)) ∨
    ENNReal.ofReal (p.N k ^ (-p.f s + ε)) < p.rho k a s (obs (p.N k) s z)}
  let AngBad : Set Incidence := {z | ENNReal.ofReal (p.N k ^ (-p.f p.L - p.S * u + ε)) <
    p.rhoA k a u (aug (p.N k) p.L u z)}
  have hnew : (mu p k a) {z | ENNReal.ofReal (p.N k ^ (-p.f r - p.S * u + 8 * ε)) <
      coarseDensity p r k a u (aug (p.N k) r u z)} ≤ (mu p k a) (Bad r) +
      (mu p k a) {z | 2 * (c / δ) * p.rho k a r (obs (p.N k) r z) <
        coarseDensity p r k a u (aug (p.N k) r u z)} := by
    apply le_trans (measure_mono ?_) (measure_union_le _ _)
    intro z hz
    by_cases hb : ENNReal.ofReal (p.N k ^ (-p.f r + ε)) < p.rho k a r (obs (p.N k) r z)
    · exact Or.inl (Or.inr hb)
    · right
      have hb' := le_of_not_gt hb
      have hbudget := angular_power_budget hN (p.f r) p.S u ε h2
      exact lt_of_le_of_lt ((mul_le_mul' le_rfl hb').trans hbudget) hz
  have hold : (mu p k a) {z | c * p.rho k a p.L (obs (p.N k) p.L z) <
      p.rhoA k a u (aug (p.N k) p.L u z)} ≤ (mu p k a) (Bad p.L) +
        (mu p k a) AngBad := by
    apply le_trans (measure_mono ?_) (measure_union_le _ _)
    intro z hz
    by_cases hb : p.rho k a p.L (obs (p.N k) p.L z) <
        ENNReal.ofReal (p.N k ^ (-p.f p.L - ε))
    · exact Or.inl (Or.inl hb)
    · right
      have hb' := le_of_not_gt hb
      have heq : c * ENNReal.ofReal (p.N k ^ (-p.f p.L - ε)) =
          ENNReal.ofReal (p.N k ^ (-p.f p.L - p.S * u + ε)) := by
        dsimp [c]
        rw [ofReal_rpow_mul_rpow hNp]
        congr 2
        ring
      change ENNReal.ofReal (p.N k ^ (-p.f p.L - p.S * u + ε)) < _
      rw [← heq]
      exact lt_of_le_of_lt (mul_le_mul' le_rfl hb') hz
  exact hnew.trans ((add_le_add le_rfl H).trans
    (add_le_add le_rfl (mul_le_mul' le_rfl (add_le_add hold le_rfl))))


private theorem weighted_error_sum {ι : Type*} [Fintype ι]
    (w a b c m : ι → ENNReal) (δ : ENNReal) :
    (∑ i, w i * (a i + 2 * (b i + c i + δ * 2 * m i))) =
      (∑ i, w i * a i) + 2 * ((∑ i, w i * b i) + (∑ i, w i * c i) +
        δ * 2 * ∑ i, w i * m i) := by
  classical
  calc
    _ = ∑ i, (w i * a i + 2 * (w i * b i + w i * c i + δ * 2 * (w i * m i))) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The angular upper-tail estimate passes to every coarser terminal depth,
with power-small exceptional mass in the original mixture. -/
theorem coarse_angular_powerSmall {p : Problem} (hp : Exact p) {r u τ : ℝ}
    (hr : 0 ≤ r) (hrL : r ≤ p.L) (hu : 0 < u) (huU : u ≤ p.U) (hτ : 0 < τ) :
    IsPowerSmall p.N (fun k => ∑ a, ENNReal.ofReal (p.w k a) *
      (mu p k a) {z | ENNReal.ofReal (p.N k ^ (-p.f r - p.S * u + τ)) <
        coarseDensity p r k a u (aug (p.N k) r u z)}) := by
  let ε := τ / 8
  have hε : 0 < ε := by dsimp [ε]; positivity
  have h8ε : 8 * ε = τ := by dsimp [ε]; ring
  let δ : ℕ → ENNReal := fun k => ENNReal.ofReal (p.N k ^ (-ε))
  have hNt : Tendsto p.N atTop atTop := hp.1.2.1
  have hR : IsPowerSmall p.N (pureBadMass p r ε) := hp.2.2.2.2.2.1 r ε hr hrL hε
  have hL : IsPowerSmall p.N (pureBadMass p p.L ε) :=
    hp.2.2.2.2.2.1 p.L ε hp.1.2.2.2.2.2.1.le le_rfl hε
  have hA : IsPowerSmall p.N (angularBadMass p u ε) := hp.2.2.2.2.2.2.2 u ε hu huU hε
  have hδ : IsPowerSmall p.N δ := ⟨ε, hε, Eventually.of_forall fun _ => le_rfl⟩
  let E : ℕ → ENNReal := fun k => pureBadMass p p.L ε k + angularBadMass p u ε k + δ k + δ k
  have hE : IsPowerSmall p.N E := ((hL.add hNt hA).add hNt hδ).add hNt hδ
  have h2 : ∀ᶠ k in atTop, 2 ≤ p.N k ^ (4 * ε) :=
    ((tendsto_rpow_atTop (by positivity : 0 < 4 * ε)).comp hNt).eventually (eventually_ge_atTop 2)
  apply (hR.add hNt (hE.add hNt hE)).mono
  filter_upwards [h2] with k hk
  have H := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin (p.1 k))))
    (fun a _ => mul_le_mul' (le_refl (ENNReal.ofReal (p.w k a)))
      (coarse_angular_world_bound hp hr hrL hu huU k a hε hk))
  rw [weighted_error_sum] at H
  simp only [h8ε] at H
  calc
    _ ≤ pureBadMass p r ε k + 2 * (pureBadMass p p.L ε k + angularBadMass p u ε k +
        δ k * 2 * ∑ a, ENNReal.ofReal (p.w k a) * (mu p k a) univ) := H
    _ ≤ pureBadMass p r ε k + 2 * (pureBadMass p p.L ε k + angularBadMass p u ε k +
        δ k * 2 * 1) := by gcongr; exact weighted_mu_univ_le_one hp k
    _ = pureBadMass p r ε k + (E k + E k) := by dsimp [E]; ring


/-- Coarsening retains the complete original geometric data and replaces only
the endpoint, its cap, the angular range, and the terminal angular density. -/
noncomputable def coarsen (p : Problem) (r d' : ℝ) : Problem :=
  ⟨p.1, p.N, p.K, p.M, p.D, r, d', p.S, p.U * r / p.L, p.w, p.nu, p.E,
    p.rho, coarseDensity p r, p.f⟩

/-- Exactness of the coarsened data, including the angular cap at its new endpoint. -/
theorem exact_coarsen {p : Problem} (hp : Exact p) {r d' : ℝ}
    (hr : 0 < r) (hrL : r < p.L) (hd' : 0 ≤ d') (hd'1 : d' < 1)
    (hcap : ∀ s : ℝ, 0 ≤ s → s ≤ r → p.f r - p.f s ≤ d' * (r - s)) :
    Exact (coarsen p r d') := by
  rcases hp with ⟨hbase, hworld, hdens, hjoint, hprofile, htypical, hcapold, hangular⟩
  rcases hbase with ⟨hN, hNt, hK, hM, hD, hL, hd, hd1, hS, hU⟩
  have hU' : p.U * r / p.L ≤ p.U := by
    apply (div_le_iff₀ hL).mpr
    nlinarith [mul_nonneg hU.le (sub_nonneg.mpr hrL.le)]
  refine ⟨⟨hN, hNt, hK, hM, hD, hr, hd', hd'1, hS, div_pos (mul_pos hU hr) hL⟩,
    hworld, ?_, ?_, ?_, ?_, hcap, ?_⟩
  · intro k a s hs hsr
    exact hdens k a s hs (hsr.trans hrL.le)
  · intro k a u hu huU
    exact coarseDensity_law ⟨⟨hN, hNt, hK, hM, hD, hL, hd, hd1, hS, hU⟩,
      hworld, hdens, hjoint, hprofile, htypical, hcapold, hangular⟩ hr.le hrL.le k a u
  · intro s t hs hst htr
    exact hprofile s t hs hst (htr.trans hrL.le)
  · intro s τ hs hsr hτ
    exact htypical s τ hs (hsr.trans hrL.le) hτ
  · intro u τ hu huU hτ
    exact coarse_angular_powerSmall ⟨⟨hN, hNt, hK, hM, hD, hL, hd, hd1, hS, hU⟩,
      hworld, hdens, hjoint, hprofile, htypical, hcapold, hangular⟩
      hr.le hrL.le hu (huU.trans hU') hτ

/-- Every true system for the coarsened problem is a known atlas at the same
depth and cost in the original problem. -/
theorem coarsen_cost_known (p : Problem) (r d' h : ℝ) (hc : Cost (coarsen p r d') h) :
    Known p r r h := by
  rcases hc with ⟨hh, B, hB, hc⟩
  refine ⟨hh, B, hB, ?_⟩
  intro ε hε
  apply (hc ε hε).mono
  intro k hk
  rcases hk with ⟨T, n, γ, j, A, C, u, v, J, P, Λ, hcd⟩
  change ChartData p B r r (h + ε) ε true k T n γ j A C u v J P Λ at hcd
  rcases hcd with ⟨ht, hn, hm, hdisj, hsub, hcharts, hlist, hlmeas, hcover, hmass⟩
  refine ⟨T, n, γ, j, A, C, u, v, J, P, Λ, ht, hn, hm, hdisj, hsub, ?_,
    hlist, hlmeas, hcover, hmass⟩
  intro i
  rcases hcharts i with ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂⟩
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁,
    fun hf => False.elim (Bool.false_ne_true hf)⟩

/-- The full angular-coarsening clause of the scalar chart calculus. -/
theorem angular_coarsening {p : Problem} (hp : Exact p) {r d' : ℝ}
    (hr : 0 < r) (hrL : r < p.L) (hd' : 0 ≤ d') (hd'1 : d' < 1)
    (hcap : ∀ s : ℝ, 0 ≤ s → s ≤ r → p.f r - p.f s ≤ d' * (r - s)) :
    ∃ q : Problem, Exact q ∧ q.L = r ∧ q.d = d' ∧ q.S = p.S ∧
      q.U = p.U * r / p.L ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ r → q.f s - q.f 0 = p.f s - p.f 0) ∧
      (∀ h : ℝ, Cost q h → Known p r r h) := by
  refine ⟨coarsen p r d', exact_coarsen hp hr hrL hd' hd'1 hcap,
    rfl, rfl, rfl, rfl, (fun _ _ _ => rfl), ?_⟩
  exact fun h hc => coarsen_cost_known p r d' h hc

end Submission.Obl.k4_scalar_chart_normalization
