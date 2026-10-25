import Submission.Obl.k4_raw_localized_native_systems.C.Q2Strips

/-
Adapted from this LOT tree, o178, session x0596, `Q2BadPair.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# The bad-pair bound for the good path of a later chart system, in one world

Instantiates `world_bad_pair_le` with the charts of a narrow system: minor-axis
normals, clipped normal speeds, unit-interval enlarged frames, dyadic blocks of
the world, the system's (measurable) terminal lists and the first-chart tags.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- Clipping to `[-K, K]`. -/
def clip (K x : ℝ) : ℝ := max (-K) (min K x)

theorem clip_eq {K x : ℝ} (h : |x| ≤ K) : clip K x = x := by
  rw [abs_le] at h
  unfold clip
  rw [min_eq_right h.2, max_eq_right h.1]

theorem abs_clip_le {K x : ℝ} (hK : 0 ≤ K) : |clip K x| ≤ K := by
  unfold clip
  rw [abs_le]
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

theorem abs_inner_le_norm' (n w : Plane) (hn : ‖n‖ = 1) : |inner ℝ n w| ≤ ‖w‖ := by
  calc |inner ℝ n w| ≤ ‖n‖ * ‖w‖ := abs_real_inner_le_norm n w
    _ = ‖w‖ := by rw [hn, one_mul]

variable {p : Data} {k : ℕ}

/-- The minor-axis normals of the charts. -/
def q2normal (a : Atlas p k) (b : Fin a.C) : Plane := minorNormal (a.Q b)

/-- Clipped normal speeds of the charts. -/
def q2speed (a : Atlas p k) (Kc : ℝ) (b : Fin a.C) : ℝ :=
  clip Kc (inner ℝ (q2normal a b) (a.u b))

/-- Clipped normal intercepts of the charts. -/
def q2intercept (a : Atlas p k) (Kc : ℝ) (b : Fin a.C) : ℝ :=
  clip Kc (inner ℝ (q2normal a b) (a.c b))

/-- The world's dyadic blocks (empty for charts of other worlds). -/
def q2blk (a : Atlas p k) (γ : Fin (p.W k)) (b : Fin a.C) : Set ℝ := by
  classical
  exact if a.γ b = γ then
    Set.Icc (((a.j b : ℕ) : ℝ) / (2 : ℝ) ^ a.T) ((((a.j b : ℕ) : ℝ) + 1) / (2 : ℝ) ^ a.T)
  else ∅

section

variable {a : Atlas p k} {γ : Fin (p.W k)} {M D : ℕ} {κ r : ℝ} {ex : Fin a.C → Prop}

/-- Along the good path, the clipped speed of the tag is its actual normal speed,
and the normal velocity offset is at most `ρ`. -/
theorem goodPath_speed (hc : ChartsHyp a M D κ r ex)
    (hdisj : ∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b'))
    (hC : 0 < a.C) {u τ κ' lam ρ Kc : ℝ}
    (hρ : ∀ b, lam ≤ ‖longCol (a.Q b)‖ → minorWidth (a.Q b) * (κ * stripScale a.T) ≤ ρ) (hKc : κ' + ρ ≤ Kc)
    {q : Point} (hq : q ∈ goodPath a γ u τ κ' lam) :
    |inner ℝ (q2normal a (tagOf a γ hC q)) (v q.1) - q2speed a Kc (tagOf a γ hC q)| ≤ ρ := by
  obtain ⟨htag, hF, hlong⟩ := goodPath_tag a γ hc hdisj hC hq
  set i := tagOf a γ hC q
  have hA : q.1 ∈ a.A i := htag.2.1
  have hvel := (hc.normal_velocity i hA).trans (hρ i hlong)
  have hn : ‖q2normal a i‖ = 1 := norm_minorNormal (hc.det_ne i)
  have hvq : ‖v q.1‖ ≤ κ' := by
    have := hq.2.2.2.2; linarith [norm_nonneg (y q.1 0)]
  have hraw : |inner ℝ (q2normal a i) (a.u i)| ≤ Kc := by
    have h1 := abs_inner_le_norm' (q2normal a i) (v q.1) hn
    have h2 : inner ℝ (q2normal a i) (a.u i) =
        inner ℝ (q2normal a i) (v q.1) - inner ℝ (q2normal a i) (v q.1 - a.u i) := by
      rw [inner_sub_right]; ring
    rw [h2]
    calc |inner ℝ (q2normal a i) (v q.1) - inner ℝ (q2normal a i) (v q.1 - a.u i)|
        ≤ |inner ℝ (q2normal a i) (v q.1)| + |inner ℝ (q2normal a i) (v q.1 - a.u i)| :=
          abs_sub _ _
      _ ≤ κ' + ρ := add_le_add (h1.trans hvq) hvel
      _ ≤ Kc := hKc
  unfold q2speed
  rw [clip_eq hraw, ← inner_sub_right]
  exact hvel

/-- Along the good path, the clipped intercept of the tag is its actual normal
intercept, and the normal position offset at time zero is at most `ρ`. -/
theorem goodPath_intercept (hc : ChartsHyp a M D κ r ex)
    (hdisj : ∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b'))
    (hC : 0 < a.C) {u τ κ' lam ρ Kc : ℝ}
    (hρ : ∀ b, lam ≤ ‖longCol (a.Q b)‖ → minorWidth (a.Q b) * (κ * stripScale a.T) ≤ ρ) (hKc : κ' + ρ ≤ Kc)
    {q : Point} (hq : q ∈ goodPath a γ u τ κ' lam) :
    |inner ℝ (q2normal a (tagOf a γ hC q)) (y q.1 0) - q2intercept a Kc (tagOf a γ hC q)| ≤ ρ := by
  obtain ⟨htag, hF, hlong⟩ := goodPath_tag a γ hc hdisj hC hq
  set i := tagOf a γ hC q
  have hA : q.1 ∈ a.A i := htag.2.1
  have hpos := (hc.normal_position_zero i hA).trans (hρ i hlong)
  have hn : ‖q2normal a i‖ = 1 := norm_minorNormal (hc.det_ne i)
  have hyq : ‖y q.1 0‖ ≤ κ' := by
    have := hq.2.2.2.2; linarith [norm_nonneg (v q.1)]
  have hraw : |inner ℝ (q2normal a i) (a.c i)| ≤ Kc := by
    have h1 := abs_inner_le_norm' (q2normal a i) (y q.1 0) hn
    have h2 : inner ℝ (q2normal a i) (a.c i) =
        inner ℝ (q2normal a i) (y q.1 0) - inner ℝ (q2normal a i) (y q.1 0 - a.c i) := by
      rw [inner_sub_right]; ring
    rw [h2]
    calc |inner ℝ (q2normal a i) (y q.1 0) - inner ℝ (q2normal a i) (y q.1 0 - a.c i)|
        ≤ |inner ℝ (q2normal a i) (y q.1 0)| + |inner ℝ (q2normal a i) (y q.1 0 - a.c i)| :=
          abs_sub _ _
      _ ≤ κ' + ρ := add_le_add (h1.trans hyq) hpos
      _ ≤ Kc := hKc
  unfold q2intercept
  rw [clip_eq hraw, ← inner_sub_right]
  exact hpos

end

/-- **Bad-pair bound of one world for a later chart system.** -/
theorem q2_world_bad_pair_le (hp : Valid p) (a : Atlas p k) (γ : Fin (p.W k))
    {M D : ℕ} {κ r : ℝ} {ex : Fin a.C → Prop} (hc : ChartsHyp a M D κ r ex)
    (hdisj : ∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b'))
    (hknown : ∀ b, ∀ z ∈ a.F b, b ∈ a.lst (a.γ b) (obs (p.B k (a.γ b)) (δ (p.N k) p.L) z))
    (κL : ℕ) (hcard : ∀ o, (a.lst γ o).card ≤ κL)
    (hmeas : ∀ b, MeasurableSet {o | b ∈ a.lst γ o})
    (hC : 0 < a.C) {u τ κ' lam ρ Kc g H : ℝ} (hu : 0 < u) (huη : u ≤ p.η * p.L)
    (hκ' : 1 ≤ κ') (hκκ' : κ ≤ κ')
    (hρ : ∀ b, lam ≤ ‖longCol (a.Q b)‖ → minorWidth (a.Q b) * (κ * stripScale a.T) ≤ ρ) (hKc : κ' + ρ ≤ Kc)
    (hg : 0 < g) (hH : 0 < H) (hpin : 8 * ρ / (g * H) ≤ δ (p.N k) u) :
    ((p.ν k γ).prod (volume.prod volume))
        {z | (z.1, z.2.1) ∈ goodPath a γ u τ κ' lam ∧ (z.1, z.2.2) ∈ goodPath a γ u τ κ' lam ∧
          g * H < min ‖q2normal a (tagOf a γ hC (z.1, z.2.1)) -
              q2normal a (tagOf a γ hC (z.1, z.2.2))‖
            ‖q2normal a (tagOf a γ hC (z.1, z.2.1)) + q2normal a (tagOf a γ hC (z.1, z.2.2))‖} ≤
      ∑ b, volume (q2blk a γ b) *
        (ENNReal.ofReal (p.N k ^ (-p.S * u + 2 * τ)) * ((9 * κL : ℕ) : ENNReal) *
          (ENNReal.ofReal (p.N k ^ (-p.f 0 + τ)) *
            ENNReal.ofReal (256 * κ' ^ 4 * (1 - 0) * |(stripScale a.T • a.Q b).det|))) := by
  classical
  have hEsub : ∀ z ∈ p.E k γ, z.2 ∈ Set.Icc (0 : ℝ) 1 := by
    obtain ⟨M', D', hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
    intro z hz
    exact (Set.mem_prod.1 (((hfmt k).2.2.2.1 γ).2.2.2.2.2.2.2.2.1 hz)).2
  refine world_bad_pair_le hp k γ (τ := τ) hu huη hκ' (q2normal a) (q2speed a Kc) a.c a.u
    (fun b => stripScale a.T • a.Q b) ?_ (q2blk a γ) (a.lst γ) κL hcard hmeas
    (goodPath a γ u τ κ' lam) (tagOf a γ hC) hg hH
    (fun b => norm_minorNormal (hc.det_ne b)) ?_ ?_ ?_ ?_ hpin
  · intro b
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (stripScale_pos a.T).ne') (hc.det_ne b)
  · intro q hq
    obtain ⟨htag, hF, hlong⟩ := goodPath_tag a γ hc hdisj hC hq
    have hsel := hc.selected _ hF
    rw [htag.1] at hsel
    exact ⟨hq.2.1, hq.2.2.1, hq.2.2.2.1, hsel.1, hEsub q hsel.1⟩
  · intro q hq
    obtain ⟨htag, hF, hlong⟩ := goodPath_tag a γ hc hdisj hC hq
    have hsel := hc.selected _ hF
    refine ⟨?_, ?_⟩
    · unfold q2blk
      rw [if_pos htag.1]
      exact hsel.2.2
    · have := hknown _ q hF
      rwa [htag.1] at this
  · intro q hq
    exact goodPath_speed hc hdisj hC hρ hKc hq
  · intro q hq t ht
    obtain ⟨htag, hF, hlong⟩ := goodPath_tag a γ hc hdisj hC hq
    exact (hc.extend _ htag.2.1 ht).trans hκκ'


end

end Submission.Obl.k4_raw_localized_native_systems.C
