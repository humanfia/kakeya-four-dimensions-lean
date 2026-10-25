import Submission.Obl.k4_raw_localized_native_systems.C.OneSample
import Submission.Obl.k4_raw_localized_native_systems.C.ForestLevel
import Submission.Obl.k4_raw_localized_native_systems.Window.NativeIdentity

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The current factory uses exactly the tangent of the raw native scalar. -/
theorem cCoeff_eq_fullTime {W C : ℕ} (P : Fin W → MvPolynomial (Fin 4) ℝ)
    (γ : Fin C → Fin W) (n : Fin C → Plane) (A : Fin C → Set Line) (a : Fin C) :
    cCoeff P γ n A a = fullTimeCoefficients (P (γ a)) (normalTangent (n a)) (A a) := by
  rw [cCoeff_eq]
  rfl

theorem cR_eq_weighted_prior {W C : ℕ} (ω : Fin W → ℝ) (ν : Fin W → Measure Line)
    (γ : Fin C → Fin W) (A : Fin C → Set Line) (a : Fin C) :
    cR ω ν γ A a = ENNReal.ofReal (ω (γ a)) * ν (γ a) (A a) := by
  simp only [cR, pow_zero, div_one, ENNReal.ofReal_one, one_mul]

/-- Both original factors are positive on the family retained by pruning. -/
theorem cR_pos {W C : ℕ} {ω : Fin W → ℝ} {ν : Fin W → Measure Line}
    {γ : Fin C → Fin W} {A : Fin C → Set Line} {a : Fin C}
    (hω : 0 < ω (γ a)) (hprior : 0 < ν (γ a) (A a)) : 0 < cR ω ν γ A a := by
  rw [cR_eq_weighted_prior]
  exact pos_iff_ne_zero.mpr (mul_ne_zero (ENNReal.ofReal_pos.mpr hω).ne' hprior.ne')

/-- Conditional full-time laws keep their original weighted domination. -/
theorem cLaws_original_domination {p : Data} (hp : Valid p) {k C : ℕ}
    (γ : Fin C → Fin (p.W k)) (A : Fin C → Set Line) (F G : Fin C → Set Point)
    (hprior : ∀ a, 0 < p.ν k (γ a) (A a)) (hGF : ∀ a, G a ⊆ F a) (a : Fin C) :
    cR (p.ω k) (p.ν k) γ A a • cLaws (p.ν k) γ A G a ≤
      ENNReal.ofReal (p.ω k (γ a)) • (priorMass p k (γ a)).restrict (F a) := by
  have : IsProbabilityMeasure (p.ν k (γ a)) := Window.valid_prob hp k (γ a)
  rw [cR_eq_weighted_prior, cLaws, cLaw, smul_smul, mul_assoc,
    ENNReal.mul_inv_cancel (hprior a).ne' (measure_ne_top _ _), mul_one]
  exact Window.smul_measure_le_smul_right _ (Measure.restrict_mono (hGF a) le_rfl)

/-- A good set contained in the raw support gives exactly the required
almost-everywhere coverage, including for laws of zero total mass. -/
theorem cLaws_compl_eq_zero {W C : ℕ} (ν : Fin W → Measure Line)
    (γ : Fin C → Fin W) (A : Fin C → Set Line) (G S : Fin C → Set Point)
    (hG : ∀ a, MeasurableSet (G a)) (hGS : ∀ a, G a ⊆ S a) (a : Fin C) :
    cLaws ν γ A G a (S a)ᶜ = 0 := by
  rw [cLaws, cLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' (hG a)]
  have hempty : (S a)ᶜ ∩ G a = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hz.1 (hGS a hz.2)
  rw [hempty, measure_empty, mul_zero]

/-- Reading the normal row of the actual inverse strip frame recovers the
physical normal width from the chart fit bound. -/
theorem stripFrame_normal_bound {n : Plane} (hn : ‖n‖ = 1) {g κ : ℝ}
    (hg : 0 < g) {w : Plane}
    (hfit : ‖Matrix.toEuclideanLin (stripFrame g n)⁻¹ w‖ ≤ κ) :
    |inner ℝ n w| ≤ κ * g := by
  have hcoord := (PiLp.norm_apply_le (Matrix.toEuclideanLin (stripFrame g n)⁻¹ w)
    (1 : Fin 2)).trans hfit
  rw [stripFrame_inv hn hg.ne', stripFrameInv_apply] at hcoord
  have hcoord' : |inner ℝ n w / g| ≤ κ := by
    simpa only [PiLp.toLp_apply, Matrix.cons_val_one, Matrix.cons_val_zero,
      Real.norm_eq_abs] using hcoord
  rw [abs_div, abs_of_pos hg, div_le_iff₀ hg] at hcoord'
  exact hcoord'

theorem CFam.measurable_events {p : Data} {k M D C : ℕ} {a : Atlas p k}
    {loss g : ℝ} {γ : Fin C → Fin (p.W k)} {n : Fin C → Plane} {int sp : Fin C → ℝ}
    {A : Fin C → Set Line} {F : Fin C → Set Point}
    {lst : Fin (p.W k) → Observation → Finset (Fin C)}
    (h : CFam p k a M D loss g γ n int sp A F lst) (c : Fin C) : MeasurableSet (F c) :=
  (h.1 c).2.2.2.2.2.2.2.1

theorem CFam.events_subset {p : Data} {k M D C : ℕ} {a : Atlas p k}
    {loss g : ℝ} {γ : Fin C → Fin (p.W k)} {n : Fin C → Plane} {int sp : Fin C → ℝ}
    {A : Fin C → Set Line} {F : Fin C → Set Point}
    {lst : Fin (p.W k) → Observation → Finset (Fin C)}
    (h : CFam p k a M D loss g γ n int sp A F lst) (c : Fin C) {z : Point} (hz : z ∈ F c) :
    z ∈ p.E k (γ c) ∧ z.1 ∈ A c ∧ z.2 ∈ Icc (0 : ℝ) 1 := by
  have hsel := (h.1 c).2.2.2.2.2.2.2.2.2.2.1 z hz
  exact ⟨hsel.1, hsel.2.1, by simpa only [pow_zero, div_one, zero_add] using hsel.2.2.1⟩

theorem CFam.events_disjoint {p : Data} {k M D C : ℕ} {a : Atlas p k}
    {loss g : ℝ} {γ : Fin C → Fin (p.W k)} {n : Fin C → Plane} {int sp : Fin C → ℝ}
    {A : Fin C → Set Line} {F : Fin C → Set Point}
    {lst : Fin (p.W k) → Observation → Finset (Fin C)}
    (h : CFam p k a M D loss g γ n int sp A F lst)
    (c c' : Fin C) (hne : c ≠ c') (hγ : γ c = γ c') : Disjoint (F c) (F c') := by
  apply Set.disjoint_left.mpr
  intro z hz hz'
  exact Set.disjoint_left.mp (h.2.2.1 c c' hne hγ)
    (h.events_subset c hz).2.1 (h.events_subset c' hz').2.1

theorem CFam.terminal_known {p : Data} {k M D C : ℕ} {a : Atlas p k}
    {loss g : ℝ} {γ : Fin C → Fin (p.W k)} {n : Fin C → Plane} {int sp : Fin C → ℝ}
    {A : Fin C → Set Line} {F : Fin C → Set Point}
    {lst : Fin (p.W k) → Observation → Finset (Fin C)}
    (h : CFam p k a M D loss g γ n int sp A F lst) (hL : p.L = 1)
    (c : Fin C) {z : Point} (hz : z ∈ F c) :
    c ∈ lst (γ c) (obs (p.B k (γ c)) (δ (p.N k) p.L) z) := by
  simpa only [hL] using (h.1 c).2.2.2.2.2.2.2.2.2.2.2 z hz

/-- The factory's indexing of each layer preserves its genuine parent
world, full assignment and selected event. -/
theorem level_atlas_ancestry {p : Data} {k M D m : ℕ} {r : ℕ → ℝ}
    (a : k4_raw_critical_segment_forests.Forest p k) (ha : a.Core M D m r) (i : ℕ)
    (lst₀ : Fin (p.W k) → Observation → Finset (Fin (levelSet a i).card))
    (lst₁ : Fin (p.W k) → Observation → Finset (Fin (levelSet a (i + 1)).card))
    (b : Fin (levelSet a (i + 1)).card) :
    ∃ e : Fin (levelSet a i).card,
      (levelAtlas a i lst₀).γ e = (levelAtlas a (i + 1) lst₁).γ b ∧
      (levelAtlas a (i + 1) lst₁).A b ⊆ (levelAtlas a i lst₀).A e ∧
      (levelAtlas a (i + 1) lst₁).F b ⊆ (levelAtlas a i lst₀).F e := by
  have hlev := levelEmb_lev a (i + 1) b
  have hpar := (ha.2.2.2.2.2 (levelEmb a (i + 1) b)).2.2.2
    (show 0 < a.lev (levelEmb a (i + 1) b) by omega)
  have hparent : a.lev (a.par (levelEmb a (i + 1) b)) = i := by omega
  obtain ⟨e, he⟩ := levelEmb_surj a hparent
  refine ⟨e, ?_, ?_, ?_⟩
  · change a.γ (levelEmb a i e) = a.γ (levelEmb a (i + 1) b)
    rw [he]
    exact hpar.2.1
  · change a.A (levelEmb a (i + 1) b) ⊆ a.A (levelEmb a i e)
    rw [he]
    exact hpar.2.2.1
  · change a.F (levelEmb a (i + 1) b) ⊆ a.F (levelEmb a i e)
    rw [he]
    exact hpar.2.2.2.1

theorem CFam.earlier_ancestry {p : Data} {k M D MC DC m C : ℕ} {r : ℕ → ℝ}
    (a : k4_raw_critical_segment_forests.Forest p k) (ha : a.Core M D m r) (i : ℕ)
    (lst₀ : Fin (p.W k) → Observation → Finset (Fin (levelSet a i).card))
    (lst₁ : Fin (p.W k) → Observation → Finset (Fin (levelSet a (i + 1)).card))
    {loss g : ℝ} {γ : Fin C → Fin (p.W k)} {n : Fin C → Plane} {int sp : Fin C → ℝ}
    {A : Fin C → Set Line} {F : Fin C → Set Point}
    {lst : Fin (p.W k) → Observation → Finset (Fin C)}
    (h : CFam p k (levelAtlas a (i + 1) lst₁) MC DC loss g γ n int sp A F lst)
    (c : Fin C) {z : Point} (hz : z ∈ F c) :
    ∃ e : Fin (levelSet a i).card,
      (levelAtlas a i lst₀).γ e = γ c ∧ z ∈ (levelAtlas a i lst₀).F e := by
  have hsource := h.2.2.2.2.2 c hz
  simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and] at hsource
  obtain ⟨b, hγ, hzb⟩ := hsource
  obtain ⟨e, heγ, -, heF⟩ := level_atlas_ancestry a ha i lst₀ lst₁ b
  exact ⟨e, heγ.trans hγ, heF hzb⟩

/-- The delivered frozen chart supplies a full-time physical normal strip,
with no extra hypothesis on the choice of the factory's representatives. -/
theorem CFam.normal_strip {p : Data} {k M D C : ℕ} {a : Atlas p k}
    {loss g : ℝ} {γ : Fin C → Fin (p.W k)} {n : Fin C → Plane} {int sp : Fin C → ℝ}
    {A : Fin C → Set Line} {F : Fin C → Set Point}
    {lst : Fin (p.W k) → Observation → Finset (Fin C)}
    (h : CFam p k a M D loss g γ n int sp A F lst) (hg : 0 < g)
    (c : Fin C) {l : Line} (hl : l ∈ A c) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    |inner ℝ (n c) (y l t) - int c - t * sp c| ≤ p.N k ^ loss * g := by
  have hfit := (((h.1 c).2.2.2.2.2.2.2.2.2.1 l hl).2.2 t
    (by simpa only [pow_zero, div_one, zero_add] using ht)).1
  have hnormal := stripFrame_normal_bound (h.2.1 c) hg hfit
  simpa only [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, h.2.1 c,
    one_pow, mul_one] using hnormal

theorem CFam.normal_speed {p : Data} {k M D C : ℕ} {a : Atlas p k}
    {loss g : ℝ} {γ : Fin C → Fin (p.W k)} {n : Fin C → Plane} {int sp : Fin C → ℝ}
    {A : Fin C → Set Line} {F : Fin C → Set Point}
    {lst : Fin (p.W k) → Observation → Finset (Fin C)}
    (h : CFam p k a M D loss g γ n int sp A F lst) (hg : 0 < g)
    (c : Fin C) {z : Point} (hz : z ∈ F c) :
    |inner ℝ (n c) (v z.1) - sp c| ≤ 2 * (p.N k ^ loss * g) := by
  have hspeed := Window.native_strip_velocity (h.2.1 c)
    (fun t ht => h.normal_strip hg c (h.events_subset c hz).2.1 ht)
  simpa only [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, h.2.1 c,
    one_pow, mul_one] using hspeed

/-- The physical data used by good-set deletion and the raw native witness
constructor, all read from the same original current family. -/
structure RawCurrentGeometry (p : Data) (k : ℕ) {C : ℕ}
    (γ : Fin C → Fin (p.W k)) (n : Fin C → Plane) (int sp : Fin C → ℝ)
    (A : Fin C → Set Line) (F : Fin C → Set Point)
    (lst : Fin (p.W k) → Observation → Finset (Fin C)) (κ g : ℝ) : Prop where
  measurableEvents : ∀ c, MeasurableSet (F c)
  originalEvents : ∀ c, F c ⊆ p.E k (γ c)
  assignmentTime : ∀ c z, z ∈ F c → z.1 ∈ A c ∧ z.2 ∈ Icc (0 : ℝ) 1
  disjointEvents : ∀ c c', c ≠ c' → γ c = γ c' → Disjoint (F c) (F c')
  normalStrip : ∀ c l, l ∈ A c → ∀ t ∈ Icc (0 : ℝ) 1,
    |inner ℝ (n c) (y l t) - int c - t * sp c| ≤ κ * g
  normalSpeed : ∀ c z, z ∈ F c → |inner ℝ (n c) (v z.1) - sp c| ≤ 2 * (κ * g)
  terminalKnown : ∀ c z, z ∈ F c → c ∈ lst (γ c) (obs (p.B k (γ c)) (δ (p.N k) p.L) z)

theorem CFam.rawGeometry {p : Data} {k M D C : ℕ} {a : Atlas p k}
    {loss g : ℝ} {γ : Fin C → Fin (p.W k)} {n : Fin C → Plane} {int sp : Fin C → ℝ}
    {A : Fin C → Set Line} {F : Fin C → Set Point}
    {lst : Fin (p.W k) → Observation → Finset (Fin C)}
    (h : CFam p k a M D loss g γ n int sp A F lst) (hg : 0 < g) (hL : p.L = 1) :
    RawCurrentGeometry p k γ n int sp A F lst (p.N k ^ loss) g := by
  exact ⟨h.measurable_events, fun c z hz => (h.events_subset c hz).1,
    fun c z hz => (h.events_subset c hz).2, h.events_disjoint,
    fun c l hl t ht => h.normal_strip hg c hl ht,
    fun c z hz => h.normal_speed hg c hz, fun c z hz => h.terminal_known hL c hz⟩

end
end Submission.Obl.k4_raw_localized_native_systems.C
