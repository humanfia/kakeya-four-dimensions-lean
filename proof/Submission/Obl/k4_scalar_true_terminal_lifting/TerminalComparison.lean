import Submission.Obl.k4_scalar_true_terminal_lifting.BaseChange
import Submission.Obl.k4_scalar_true_terminal_lifting.CoarseLists
import Submission.Obl.k4_scalar_true_terminal_lifting.RefinementData
import Submission.Obl.k4_scalar_true_terminal_lifting.GroupedDensity
import Submission.Obl.k4_scalar_true_terminal_lifting.ListMultiplicity
import Submission.Obl.k4_scalar_true_terminal_lifting.RatioNumerics
import Submission.Obl.k4_scalar_crop_profile_transport.LabelTail
import Submission.Obl.k4_scalar_crop_profile_transport.Geometry

noncomputable section

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open MeasureTheory Set
open scoped ENNReal
open k4_scalar_linear_critical_extremizers.Split

namespace RefinementData

variable {p q : Code} {r b h : ℝ}

def dt (s : RefinementData p q r b h) (k : ℕ) : ℝ := ((2 : ℝ) ^ s.T k)⁻¹

def startTime (s : RefinementData p q r b h) (k : ℕ) (i : Fin (W q k)) : ℝ :=
  (s.j k i : ℕ) * s.dt k

def stateMap (s : RefinementData p q r b h) (k : ℕ) (i : Fin (W q k)) : State → State :=
  normalizeState (s.θ k i) (s.dt k) (s.startTime k i)

def rawDensity (s : RefinementData p q r b h) (k : ℕ) (i : Fin (W q k))
    (z : Observation) : ℝ≥0∞ :=
  (ν p (s.φ k) (s.γ k i) (s.A k i) / ENNReal.ofReal (s.J k i)) *
    g q k i (L q) (observationEquiv (s.dt k) (s.J k i) (s.u k i) (s.v k i)
      (s.startTime k i) (s.timeWidth_pos k).ne' (s.positionWidth_pos k i).ne' z)

def terminalList (s : RefinementData p q r b h) (k : ℕ) (a : Fin (W p (s.φ k))) :
    Observation → Finset (Fin (W q k)) :=
  coarsenList (s.Λ k a) (N p (s.φ k) ^ (-b)) (N p (s.φ k) ^ (-L p))

variable (s : RefinementData p q r b h)

theorem measurable_stateMap (k : ℕ) (i : Fin (W q k)) : Measurable (s.stateMap k i) :=
  measurable_normalizeState (s.measurable_θ k i) _ _

theorem rawDensity_measurable (hq : Exact q) (k : ℕ) (i : Fin (W q k)) :
    Measurable (s.rawDensity k i) := by
  have hLq : 0 ≤ L q := (hq.1.2.2.2.2.2.1).le
  exact measurable_const.mul (((hq.2.2.1 k i (L q) hLq le_rfl).1).comp
    (observationEquiv (s.dt k) (s.J k i) (s.u k i) (s.v k i) (s.startTime k i)
      (s.timeWidth_pos k).ne' (s.positionWidth_pos k i).ne').measurable)

theorem rawDensity_law (hp : Exact p) (hq : Exact q) (hL : L q = L p - r)
    (k : ℕ) (i : Fin (W q k)) :
    ((mu p (s.φ k) (s.γ k i)).restrict (s.C k i)).map
      (residualObservation (N p (s.φ k)) (L p) (s.P k i)) =
        reference.withDensity (s.rawDensity k i) := by
  have hN : 0 < N p (s.φ k) := lt_of_lt_of_le (by norm_num) (hp.1.1 (s.φ k))
  have hLq : 0 ≤ L q := (hq.1.2.2.2.2.2.1).le
  let G := g q k i (L q)
  have hG : Measurable G := (hq.2.2.1 k i (L q) hLq le_rfl).1
  have htarget : (mu q k i).map (k4_scalar_crop_profile_transport.Obs (N q k) (L q)) =
      reference.withDensity G := (hq.2.2.1 k i (L q) hLq le_rfl).2
  rw [s.resolution k, hL] at htarget
  have hcommute := terminal_observation_commutes hN (L p) r (s.dt k) (s.J k i)
    (s.u k i) (s.v k i) (s.startTime k i) (s.timeWidth_pos k) (s.positionWidth_pos k i)
    (s.P k i) (s.θ k i) (s.y_θ k i) (s.x_θ k i)
  exact raw_terminal_density_law (s.dt k) (s.J k i) (s.u k i) (s.v k i)
    (s.startTime k i) (s.timeWidth_pos k) (s.positionWidth_pos k i)
    (ν p (s.φ k) (s.γ k i) (s.A k i)) (s.prior_pos k i).ne' (s.prior_ne_top hp k i)
    ((mu p (s.φ k) (s.γ k i)).restrict (s.C k i)) (mu q k i) (s.stateMap k i)
    (s.measurable_stateMap k i)
    (residualObservation (N p (s.φ k)) (L p) (s.P k i))
    (k4_scalar_crop_profile_transport.Obs (N p (s.φ k)) (L p - r))
    (measurable_residualObservation _ _ _) (k4_scalar_crop_profile_transport.measurable_Obs _ _)
    hcommute (s.selected_law k i) G hG htarget

theorem rawDensity_evaluation (hp : Exact p) (hL : L q = L p - r)
    (k : ℕ) (i : Fin (W q k)) (z : State) :
    s.rawDensity k i (residualObservation (N p (s.φ k)) (L p) (s.P k i) z) =
      (ν p (s.φ k) (s.γ k i) (s.A k i) / ENNReal.ofReal (s.J k i)) *
        g q k i (L q) (k4_scalar_crop_profile_transport.Obs (N q k) (L q) (s.stateMap k i z)) := by
  have hN : 0 < N p (s.φ k) := lt_of_lt_of_le (by norm_num) (hp.1.1 (s.φ k))
  have hc := terminal_observation_commutes hN (L p) r (s.dt k) (s.J k i)
    (s.u k i) (s.v k i) (s.startTime k i) (s.timeWidth_pos k) (s.positionWidth_pos k i)
    (s.P k i) (s.θ k i) (s.y_θ k i) (s.x_θ k i)
  unfold rawDensity
  congr 2
  rw [s.resolution k, hL]
  exact (congrFun hc z).symm

theorem terminalList_measurable (k : ℕ) (a : Fin (W p (s.φ k))) (i : Fin (W q k)) :
    MeasurableSet {z | i ∈ s.terminalList k a z} :=
  measurableSet_mem_coarsenList (s.Λ k a) (s.measurable_list k a) _ _ i

theorem terminalList_card (k : ℕ) (a : Fin (W p (s.φ k))) (z : Observation) :
    ((s.terminalList k a z).card : ℝ≥0∞) ≤ 2 * ENNReal.ofReal (N p (s.φ k) ^ s.loss k) := by
  apply card_coarsenList_le
  intro z
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (s.list_card k a z)

theorem terminalList_known (hp : Exact p) (hb : b ≤ L p) (k : ℕ) (i : Fin (W q k)) :
    ∀ᵐ z ∂(mu p (s.φ k) (s.γ k i)).restrict (s.C k i),
      i ∈ s.terminalList k (s.γ k i) (k4_scalar_crop_profile_transport.Obs (N p (s.φ k)) (L p) z) := by
  have hN : 1 ≤ N p (s.φ k) := (by norm_num : (1 : ℝ) ≤ 2).trans (hp.1.1 (s.φ k))
  have hw : 0 < N p (s.φ k) ^ (-L p) := Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hN) _
  have hww : N p (s.φ k) ^ (-L p) ≤ N p (s.φ k) ^ (-b) :=
    Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hb)
  filter_upwards [s.list_known k i] with z hz
  exact mem_coarsenList_of_mem _ hw hww hz

theorem old_weighted_mass_le_one (hp : Exact p) (k : ℕ) :
    (∑ a : Fin (W p (s.φ k)), ENNReal.ofReal (ω p (s.φ k) a) *
      mu p (s.φ k) a univ) ≤ 1 := by
  have hmass (a : Fin (W p (s.φ k))) : mu p (s.φ k) a univ ≤ 1 := by
    letI : IsProbabilityMeasure (ν p (s.φ k) a) := ((hp.2.1 (s.φ k)).2.2.2.1 a).1
    exact k4_scalar_crop_profile_transport.selected_mass_le_one (ν p (s.φ k) a)
      (E p (s.φ k) a) ((hp.2.1 (s.φ k)).2.2.2.1 a).2.2.2.2.1
  calc
    _ ≤ ∑ a : Fin (W p (s.φ k)), ENNReal.ofReal (ω p (s.φ k) a) * 1 :=
      Finset.sum_le_sum fun a _ => mul_le_mul' le_rfl (hmass a)
    _ = 1 := by
      simp only [mul_one]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => (hp.2.1 (s.φ k)).2.1 a),
        (hp.2.1 (s.φ k)).2.2.1]
      norm_num

theorem terminal_density_integral (hp : Exact p) (k : ℕ) (a : Fin (W p (s.φ k))) :
    (∫⁻ c : Fin 2 → ℝ, ∑' v : ℤ, g p (s.φ k) a (L p) (c, v) ∂volume) =
      mu p (s.φ k) a univ := by
  have hLp : 0 ≤ L p := (hp.1.2.2.2.2.2.1).le
  have hG := (hp.2.2.1 (s.φ k) a (L p) hLp le_rfl).1
  have hlaw := (hp.2.2.1 (s.φ k) a (L p) hLp le_rfl).2
  calc
    _ = ∫⁻ z, g p (s.φ k) a (L p) z ∂reference := by
      rw [lintegral_prod _ hG.aemeasurable]
      simp only [lintegral_count]
    _ = reference.withDensity (g p (s.φ k) a (L p)) univ := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    _ = _ := by
      rw [← hlaw]
      change (mu p (s.φ k) a).map
        (k4_scalar_crop_profile_transport.Obs (N p (s.φ k)) (L p)) univ = _
      rw [Measure.map_apply (k4_scalar_crop_profile_transport.measurable_Obs _ _)
        MeasurableSet.univ, preimage_univ]

theorem rawDensity_lower_tail (hp : Exact p) (hq : Exact q) (hL : L q = L p - r)
    (hb : b ≤ L p) (k : ℕ) (η : ℝ≥0∞) :
    (∑ i : Fin (W q k), ENNReal.ofReal (ω p (s.φ k) (s.γ k i)) *
      (mu p (s.φ k) (s.γ k i)).restrict (s.C k i)
        {z | s.rawDensity k i (residualObservation (N p (s.φ k)) (L p) (s.P k i) z) <
          η * g p (s.φ k) (s.γ k i) (L p)
            (k4_scalar_crop_profile_transport.Obs (N p (s.φ k)) (L p) z)}) ≤
      η * (4 * ENNReal.ofReal (N p (s.φ k) ^ s.loss k)) := by
  have hLp : 0 ≤ L p := (hp.1.2.2.2.2.2.1).le
  let source := fun i : Fin (W q k) => (mu p (s.φ k) (s.γ k i)).restrict (s.C k i)
  let base := fun z : State => (k4_scalar_crop_profile_transport.Obs (N p (s.φ k)) (L p) z).1
  let fine := fun i : Fin (W q k) => fun z : State =>
    (residualObservation (N p (s.φ k)) (L p) (s.P k i) z).2
  let coarse := fun z : State => (k4_scalar_crop_profile_transport.Obs (N p (s.φ k)) (L p) z).2
  let G := fun i : Fin (W q k) => fun c v => s.rawDensity k i (c, v)
  let F := fun a : Fin (W p (s.φ k)) => fun c v => g p (s.φ k) a (L p) (c, v)
  have hG (i : Fin (W q k)) (v : ℤ) : Measurable (fun c => G i c v) :=
    (s.rawDensity_measurable hq k i).comp (measurable_id.prodMk measurable_const)
  have hF (a : Fin (W p (s.φ k))) (v : ℤ) : Measurable (fun c => F a c v) :=
    ((hp.2.2.1 (s.φ k) a (L p) hLp le_rfl).1).comp
      (measurable_id.prodMk measurable_const)
  have hs (i : Fin (W q k)) (v : ℤ) (U : Set (Fin 2 → ℝ)) (hU : MeasurableSet U) :
      source i {z | fine i z = v ∧ base z ∈ U} = ∫⁻ c in U, G i c v ∂volume :=
    k4_scalar_crop_profile_transport.label_density_slice volume (source i) base
      (k4_scalar_crop_profile_transport.measurable_Obs _ _).fst (fine i)
      (measurable_residualObservation _ _ _).snd (s.rawDensity k i)
      (s.rawDensity_measurable hq k i) (s.rawDensity_law hp hq hL k i) v U hU
  let shift := fun i : Fin (W q k) => fun c : Fin 2 → ℝ =>
    ⌊-MvPolynomial.eval c (s.P k i) / N p (s.φ k) ^ (-L p)⌋
  have hshift (i : Fin (W q k)) : Measurable (shift i) :=
    Int.measurable_floor.comp (((s.P k i).continuous_eval.measurable.neg).div_const _)
  have hbins (i : Fin (W q k)) : ∀ᵐ z ∂source i,
      fine i z = coarse z + shift i (base z) ∨
        fine i z = coarse z + shift i (base z) + 1 :=
    Filter.Eventually.of_forall (residual_hidden_bin_cases _ _ _)
  have hbound := grouped_listed_shift_density_lower_tail source volume base (s.γ k) fine coarse
    G F hG hF hs (s.terminalList k) (s.terminalList_measurable k)
    (s.terminalList_known hp hb k) shift hshift hbins
    (2 * ENNReal.ofReal (N p (s.φ k) ^ s.loss k)) (s.terminalList_card k)
    (fun a => ENNReal.ofReal (ω p (s.φ k) a)) η
  dsimp only [F] at hbound
  simp_rw [s.terminal_density_integral hp k] at hbound
  calc
    _ ≤ η * (2 * (2 * ENNReal.ofReal (N p (s.φ k) ^ s.loss k))) *
        ∑ a : Fin (W p (s.φ k)), ENNReal.ofReal (ω p (s.φ k) a) * mu p (s.φ k) a univ := hbound
    _ ≤ η * (2 * (2 * ENNReal.ofReal (N p (s.φ k) ^ s.loss k))) * 1 :=
      mul_le_mul' le_rfl (s.old_weighted_mass_le_one hp k)
    _ = _ := by ring

theorem weights_ennreal (hp : Exact p) (k : ℕ) (i : Fin (W q k)) :
    ENNReal.ofReal (ω q k i) =
      (ENNReal.ofReal (ω p (s.φ k) (s.γ k i)) *
        (ENNReal.ofReal (s.dt k) * ν p (s.φ k) (s.γ k i) (s.A k i))) /
          ENNReal.ofReal (s.Z k) := by
  have hw : 0 ≤ ω p (s.φ k) (s.γ k i) := (hp.2.1 (s.φ k)).2.1 (s.γ k i)
  rw [s.weights, ENNReal.ofReal_div_of_pos (s.Z_pos k),
    ENNReal.ofReal_mul (mul_nonneg hw (s.timeWidth_pos k).le),
    ENNReal.ofReal_mul hw, ENNReal.ofReal_toReal (s.prior_ne_top hp k i), mul_assoc]
  rfl

theorem weighted_selected_transport (hp : Exact p) (k : ℕ) (i : Fin (W q k))
    (U : Set State) (hU : MeasurableSet U) :
    ENNReal.ofReal (ω q k i) * mu q k i U =
      (ENNReal.ofReal (s.Z k))⁻¹ * ENNReal.ofReal (ω p (s.φ k) (s.γ k i)) *
        (mu p (s.φ k) (s.γ k i)).restrict (s.C k i) (s.stateMap k i ⁻¹' U) := by
  have hb0 : ENNReal.ofReal (s.dt k) * ν p (s.φ k) (s.γ k i) (s.A k i) ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_ne_zero_iff.mpr (s.timeWidth_pos k)) (s.prior_pos k i).ne'
  have hbt : ENNReal.ofReal (s.dt k) * ν p (s.φ k) (s.γ k i) (s.A k i) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (s.prior_ne_top hp k i)
  rw [s.weights_ennreal hp, s.selected_law, Measure.smul_apply, smul_eq_mul]
  change (ENNReal.ofReal (ω p (s.φ k) (s.γ k i)) *
      (ENNReal.ofReal (s.dt k) * ν p (s.φ k) (s.γ k i) (s.A k i)) / ENNReal.ofReal (s.Z k)) *
    ((ENNReal.ofReal (s.dt k) * ν p (s.φ k) (s.γ k i) (s.A k i))⁻¹ *
      (Measure.map (s.stateMap k i)
        ((mu p (s.φ k) (s.γ k i)).restrict (s.C k i))) U) = _
  rw [Measure.map_apply (s.measurable_stateMap k i) hU]
  calc
    _ = (ENNReal.ofReal (s.Z k))⁻¹ * ENNReal.ofReal (ω p (s.φ k) (s.γ k i)) *
        ((ENNReal.ofReal (s.dt k) * ν p (s.φ k) (s.γ k i) (s.A k i)) *
          (ENNReal.ofReal (s.dt k) * ν p (s.φ k) (s.γ k i) (s.A k i))⁻¹) *
        (mu p (s.φ k) (s.γ k i)).restrict (s.C k i) (s.stateMap k i ⁻¹' U) := by
      rw [div_eq_mul_inv]
      ring
    _ = _ := by rw [ENNReal.mul_inv_cancel hb0 hbt, mul_one]

def oldLowerEvent (τ : ℝ) (k : ℕ) (a : Fin (W p (s.φ k))) : Set State :=
  {z | g p (s.φ k) a (L p) (k4_scalar_crop_profile_transport.Obs (N p (s.φ k)) (L p) z) <
    ENNReal.ofReal (N p (s.φ k) ^ (-f p (L p) - τ))}

def newUpperEvent (s : RefinementData p q r b h) (τ : ℝ) (k : ℕ) (i : Fin (W q k)) : Set State :=
  {z | ENNReal.ofReal (N q k ^ (-f q (L q) + τ)) <
    g q k i (L q) (k4_scalar_crop_profile_transport.Obs (N q k) (L q) z)}

def selectedLowEvent (η : ℝ≥0∞) (k : ℕ) (i : Fin (W q k)) : Set State :=
  {z | s.rawDensity k i (residualObservation (N p (s.φ k)) (L p) (s.P k i) z) <
    η * g p (s.φ k) (s.γ k i) (L p)
      (k4_scalar_crop_profile_transport.Obs (N p (s.φ k)) (L p) z)}

def oldLowerMass (τ : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ∑ a : Fin (W p (s.φ k)), ENNReal.ofReal (ω p (s.φ k) a) *
    mu p (s.φ k) a (s.oldLowerEvent τ k a)

def newUpperMass (τ : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ∑ i : Fin (W q k), ENNReal.ofReal (ω q k i) * mu q k i (s.newUpperEvent τ k i)

theorem newUpperEvent_measurable (hq : Exact q) (τ : ℝ) (k : ℕ) (i : Fin (W q k)) :
    MeasurableSet (s.newUpperEvent τ k i) := by
  have hLq : 0 ≤ L q := (hq.1.2.2.2.2.2.1).le
  exact measurableSet_lt measurable_const (((hq.2.2.1 k i (L q) hLq le_rfl).1).comp
    (k4_scalar_crop_profile_transport.measurable_Obs _ _))

theorem selected_oldLowerMass_le (τ : ℝ) (k : ℕ) :
    (∑ i : Fin (W q k), ENNReal.ofReal (ω p (s.φ k) (s.γ k i)) *
      (mu p (s.φ k) (s.γ k i)).restrict (s.C k i) (s.oldLowerEvent τ k (s.γ k i))) ≤
        ENNReal.ofReal (N p (s.φ k) ^ s.loss k) * s.oldLowerMass τ k := by
  refine grouped_restriction_mass_le (mu p (s.φ k)) (s.γ k) (s.C k)
    (s.measurable_selection k)
    (fun a z => s.Λ k a (k4_scalar_crop_profile_transport.Obs (N p (s.φ k)) b z))
    (s.list_known k) (ENNReal.ofReal (N p (s.φ k) ^ s.loss k)) ?_
    (fun a => ENNReal.ofReal (ω p (s.φ k) a)) (s.oldLowerEvent τ k)
  intro a z
  simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal (s.list_card k a _)

theorem badWorld_event_cover (hp : Exact p) (hL : L q = L p - r)
    (δ τ : ℝ) (k : ℕ) (i : Fin (W q k))
    (hbad : ν p (s.φ k) (s.γ k i) (s.A k i) <
      ENNReal.ofReal (N q k ^ (f q (L q) - f p (L p) - δ) * s.J k i)) :
    univ ⊆ (s.stateMap k i ⁻¹' s.newUpperEvent τ k i) ∪
      s.oldLowerEvent τ k (s.γ k i) ∪
        s.selectedLowEvent (ENNReal.ofReal (N p (s.φ k) ^ (-δ + 2 * τ))) k i := by
  intro z _
  by_cases hqz : s.stateMap k i z ∈ s.newUpperEvent τ k i
  · exact Or.inl (Or.inl hqz)
  by_cases hpz : z ∈ s.oldLowerEvent τ k (s.γ k i)
  · exact Or.inl (Or.inr hpz)
  apply Or.inr
  have hN : 0 < N p (s.φ k) := lt_of_lt_of_le (by norm_num) (hp.1.1 (s.φ k))
  have hold : ENNReal.ofReal (N p (s.φ k) ^ (-f p (L p) - τ)) ≤
      g p (s.φ k) (s.γ k i) (L p)
        (k4_scalar_crop_profile_transport.Obs (N p (s.φ k)) (L p) z) := not_lt.mp hpz
  have hnewq : g q k i (L q)
      (k4_scalar_crop_profile_transport.Obs (N q k) (L q) (s.stateMap k i z)) ≤
        ENNReal.ofReal (N q k ^ (-f q (L q) + τ)) := not_lt.mp hqz
  have hnew : g q k i (L q)
      (k4_scalar_crop_profile_transport.Obs (N q k) (L q) (s.stateMap k i z)) ≤
        ENNReal.ofReal (N p (s.φ k) ^ (-f q (L q) + τ)) := by
    simpa only [s.resolution k] using hnewq
  have hbad' : ν p (s.φ k) (s.γ k i) (s.A k i) <
      ENNReal.ofReal (N p (s.φ k) ^ (f q (L q) - f p (L p) - δ) * s.J k i) := by
    simpa only [s.resolution k] using hbad
  change s.rawDensity k i (residualObservation (N p (s.φ k)) (L p) (s.P k i) z) < _
  rw [s.rawDensity_evaluation hp hL]
  exact ratio_bad_implies_low_density hN (s.positionWidth_pos k i)
    (f p (L p)) (f q (L q)) δ τ _ _ _ hbad' hold hnew

theorem badMass_finite_bound (hp : Exact p) (hq : Exact q) (hL : L q = L p - r)
    (hb : b ≤ L p) (δ τ : ℝ) (k : ℕ) :
    badMass p q s.φ s.γ s.A s.J δ k ≤ s.newUpperMass τ k +
      (ENNReal.ofReal (s.Z k))⁻¹ *
        (ENNReal.ofReal (N p (s.φ k) ^ s.loss k) * s.oldLowerMass τ k +
          ENNReal.ofReal (N p (s.φ k) ^ (-δ + 2 * τ)) *
            (4 * ENNReal.ofReal (N p (s.φ k) ^ s.loss k))) := by
  classical
  let η := ENNReal.ofReal (N p (s.φ k) ^ (-δ + 2 * τ))
  let source := fun i : Fin (W q k) => (mu p (s.φ k) (s.γ k i)).restrict (s.C k i)
  let c := (ENNReal.ofReal (s.Z k))⁻¹
  let w := fun i : Fin (W q k) => ENNReal.ofReal (ω p (s.φ k) (s.γ k i))
  have hi (i : Fin (W q k)) :
      (if ν p (s.φ k) (s.γ k i) (s.A k i) <
        ENNReal.ofReal (N q k ^ (f q (L q) - f p (L p) - δ) * s.J k i) then
          ENNReal.ofReal (ω q k i) * mu q k i univ else 0) ≤
      ENNReal.ofReal (ω q k i) * mu q k i (s.newUpperEvent τ k i) +
        c * w i * source i (s.oldLowerEvent τ k (s.γ k i)) +
          c * w i * source i (s.selectedLowEvent η k i) := by
    by_cases hbad : ν p (s.φ k) (s.γ k i) (s.A k i) <
      ENNReal.ofReal (N q k ^ (f q (L q) - f p (L p) - δ) * s.J k i)
    · rw [ite_eq_left hbad, s.weighted_selected_transport hp k i univ MeasurableSet.univ,
        preimage_univ]
      have hm : source i univ ≤
          source i (s.stateMap k i ⁻¹' s.newUpperEvent τ k i) +
            source i (s.oldLowerEvent τ k (s.γ k i)) +
              source i (s.selectedLowEvent η k i) := by
        calc
          _ ≤ source i ((s.stateMap k i ⁻¹' s.newUpperEvent τ k i) ∪
              s.oldLowerEvent τ k (s.γ k i) ∪ s.selectedLowEvent η k i) :=
            measure_mono (s.badWorld_event_cover hp hL δ τ k i hbad)
          _ ≤ _ := (measure_union_le _ _).trans
            (add_le_add (measure_union_le _ _) le_rfl)
      calc
        _ ≤ c * w i * (source i (s.stateMap k i ⁻¹' s.newUpperEvent τ k i) +
            source i (s.oldLowerEvent τ k (s.γ k i)) + source i (s.selectedLowEvent η k i)) :=
          mul_le_mul' le_rfl hm
        _ = _ := by
          rw [s.weighted_selected_transport hp k i _ (s.newUpperEvent_measurable hq τ k i)]
          ring
    · rw [ite_eq_right hbad]
      exact zero_le
  unfold badMass
  calc
    _ ≤ ∑ i : Fin (W q k), (ENNReal.ofReal (ω q k i) * mu q k i (s.newUpperEvent τ k i) +
        c * w i * source i (s.oldLowerEvent τ k (s.γ k i)) +
          c * w i * source i (s.selectedLowEvent η k i)) := Finset.sum_le_sum fun i _ => hi i
    _ = s.newUpperMass τ k + c *
        ((∑ i : Fin (W q k), w i * source i (s.oldLowerEvent τ k (s.γ k i))) +
          ∑ i : Fin (W q k), w i * source i (s.selectedLowEvent η k i)) := by
      simp only [newUpperMass, Finset.sum_add_distrib, mul_add, Finset.mul_sum,
        mul_assoc, add_assoc]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul' le_rfl
      (add_le_add (s.selected_oldLowerMass_le τ k) (s.rawDensity_lower_tail hp hq hL hb k η)))

end RefinementData

end Submission.Obl.k4_scalar_true_terminal_lifting
