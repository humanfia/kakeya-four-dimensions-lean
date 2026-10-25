import Submission.Obl.k4_raw_localized_native_systems.C.FixedTimeTotal
import Submission.Obl.k4_raw_localized_native_systems.C.CLists

/-
Adapted from this LOT tree, o178, session x0596, `CMass.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# Mass of the full-time charts

An incidence of the good path whose line is on the good path at the binning time
`t₀` in the bin of a representative, whose tags at the two times are not
transverse, and whose line has the problem's native bounds on the unit interval,
is selected by the full-time chart of that representative.  Hence, in each world,
the retained mass of paired full-time binning is at most the mass of the full-time
charts plus the transverse mass at `t₀`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

variable {p : Data} {k : ℕ}

/-- The native bounds of the problem along a whole line. -/
def NativeLine (p : Data) (k : ℕ) (γ : Fin (p.W k)) (K : ℝ) (l : Line) : Prop :=
  ∀ t ∈ Set.Icc (0 : ℝ) 1, |MvPolynomial.eval (x l t) (p.P k γ)| ≤ K ∧
    |MvPolynomial.eval (x l t) (MvPolynomial.pderiv 3 (p.P k γ))| ≤ K * p.B k γ ∧
    |MvPolynomial.eval (x l t) (MvPolynomial.pderiv 3 (MvPolynomial.pderiv 3 (p.P k γ)))| ≤
      K * p.B k γ ^ 2

theorem ae_nativeLine (hp : Valid p) (k : ℕ) (γ : Fin (p.W k)) {K : ℝ} (hK : p.K k ≤ K) :
    ∀ᵐ l ∂(p.ν k γ), NativeLine p k γ K l := by
  obtain ⟨M, D, hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  have hB := hp.B_pos k γ
  filter_upwards [((hfmt k).2.2.2.1 γ).2.2.2.2.2.2.2.2.2.2.2.1] with l hl
  intro t ht
  obtain ⟨-, h1, h2, h3⟩ := hl t ht
  refine ⟨h1.trans hK, h2.trans ?_, h3.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right hK hB.le
  · exact mul_le_mul_of_nonneg_right hK (by positivity)

section

variable {a : Atlas p k} {γ : Fin (p.W k)} {M D : ℕ} {κ r : ℝ} {ex : Fin a.C → Prop}

theorem raw_intercept_le (hc : ChartsHyp a M D κ r ex) {b : Fin a.C} {l : Line} (hl : l ∈ a.A b)
    {κ' ρ Kc lam : ℝ}
    (hρ : ∀ b, lam ≤ ‖longCol (a.Q b)‖ → minorWidth (a.Q b) * (κ * stripScale a.T) ≤ ρ)
    (hlong : lam ≤ ‖longCol (a.Q b)‖) (hKc : κ' + ρ ≤ Kc) (hy : ‖y l 0‖ ≤ κ') :
    |inner ℝ (q2normal a b) (a.c b)| ≤ Kc := by
  have hpos := (hc.normal_position_zero b hl).trans (hρ b hlong)
  have hn : ‖q2normal a b‖ = 1 := norm_minorNormal (hc.det_ne b)
  have h1 := abs_inner_le_norm' (q2normal a b) (y l 0) hn
  have h2 : inner ℝ (q2normal a b) (a.c b) =
      inner ℝ (q2normal a b) (y l 0) - inner ℝ (q2normal a b) (y l 0 - a.c b) := by
    rw [inner_sub_right]; ring
  rw [h2]
  calc |inner ℝ (q2normal a b) (y l 0) - inner ℝ (q2normal a b) (y l 0 - a.c b)|
      ≤ |inner ℝ (q2normal a b) (y l 0)| + |inner ℝ (q2normal a b) (y l 0 - a.c b)| :=
        abs_sub _ _
    _ ≤ κ' + ρ := add_le_add (h1.trans hy) hpos
    _ ≤ Kc := hKc

theorem raw_speed_le (hc : ChartsHyp a M D κ r ex) {b : Fin a.C} {l : Line} (hl : l ∈ a.A b)
    {κ' ρ Kc lam : ℝ}
    (hρ : ∀ b, lam ≤ ‖longCol (a.Q b)‖ → minorWidth (a.Q b) * (κ * stripScale a.T) ≤ ρ)
    (hlong : lam ≤ ‖longCol (a.Q b)‖) (hKc : κ' + ρ ≤ Kc) (hv : ‖v l‖ ≤ κ') :
    |inner ℝ (q2normal a b) (a.u b)| ≤ Kc := by
  have hvel := (hc.normal_velocity b hl).trans (hρ b hlong)
  have hn : ‖q2normal a b‖ = 1 := norm_minorNormal (hc.det_ne b)
  have h1 := abs_inner_le_norm' (q2normal a b) (v l) hn
  have h2 : inner ℝ (q2normal a b) (a.u b) =
      inner ℝ (q2normal a b) (v l) - inner ℝ (q2normal a b) (v l - a.u b) := by
    rw [inner_sub_right]; ring
  rw [h2]
  calc |inner ℝ (q2normal a b) (v l) - inner ℝ (q2normal a b) (v l - a.u b)|
      ≤ |inner ℝ (q2normal a b) (v l)| + |inner ℝ (q2normal a b) (v l - a.u b)| := abs_sub _ _
    _ ≤ κ' + ρ := add_le_add (h1.trans hv) hvel
    _ ≤ Kc := hKc

/-- Two strips through the same bounded line with nearly parallel normals have nearly
equal coefficients. -/
theorem coeff_close {n n' : Plane} {w : Plane} {c c' ρ θ K : ℝ}
    (h : |inner ℝ n w - c| ≤ ρ) (h' : |inner ℝ n' w - c'| ≤ ρ) (hθ : ‖n - n'‖ ≤ θ)
    (hw : ‖w‖ ≤ K) (hθ0 : 0 ≤ θ) : |c - c'| ≤ 2 * ρ + θ * K := by
  have h1 : |inner ℝ (n - n') w| ≤ θ * K := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul hθ hw (norm_nonneg _) hθ0
  have h2 : c - c' = -(inner ℝ n w - c) + (inner ℝ n' w - c') + inner ℝ (n - n') w := by
    rw [inner_sub_left]; ring
  rw [h2]
  have := abs_add_le (-(inner ℝ n w - c) + (inner ℝ n' w - c')) (inner ℝ (n - n') w)
  have := abs_add_le (-(inner ℝ n w - c)) (inner ℝ n' w - c')
  rw [abs_neg] at this
  linarith

theorem coeff_close_neg {n n' : Plane} {w : Plane} {c c' ρ θ K : ℝ}
    (h : |inner ℝ n w - c| ≤ ρ) (h' : |inner ℝ n' w - c'| ≤ ρ) (hθ : ‖n + n'‖ ≤ θ)
    (hw : ‖w‖ ≤ K) (hθ0 : 0 ≤ θ) : |c + c'| ≤ 2 * ρ + θ * K := by
  have h1 : |inner ℝ (n + n') w| ≤ θ * K := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul hθ hw (norm_nonneg _) hθ0
  have h2 : c + c' = -(inner ℝ n w - c) - (inner ℝ n' w - c') + inner ℝ (n + n') w := by
    rw [inner_add_left]; ring
  rw [h2]
  have := abs_add_le (-(inner ℝ n w - c) - (inner ℝ n' w - c')) (inner ℝ (n + n') w)
  have := abs_sub (-(inner ℝ n w - c)) (inner ℝ n' w - c')
  rw [abs_neg] at this
  linarith

theorem norm_sub_le_of_bin {a : Atlas p k} {G : ℝ} {b b' : Fin a.C}
    (h0 : |q2normal a b 0 - q2normal a b' 0| < G) (h1 : |q2normal a b 1 - q2normal a b' 1| < G) :
    ‖q2normal a b - q2normal a b'‖ ≤ 2 * G := by
  refine (norm_le_abs_add_abs_fin2 _).trans ?_
  simp only [PiLp.sub_apply]
  linarith

/-- **A good pair is selected by the full-time chart of its bin.** -/
theorem goodPair_mem_cF (hc : ChartsHyp a M D κ r ex)
    (hdisj : ∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b'))
    (hEsub : p.E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1) (hB : 0 < p.B k γ)
    (hC : 0 < a.C) {u τ κ' lam ρ Kc g H G gC κC : ℝ}
    (hρ : ∀ b, lam ≤ ‖longCol (a.Q b)‖ → minorWidth (a.Q b) * (κ * stripScale a.T) ≤ ρ)
    (hKc : κ' + ρ ≤ Kc) (hG : 0 < G) (hθ0 : 0 ≤ g * H)
    (hθG : g * H ≤ G) (hρG : 2 * ρ + g * H * κ' ≤ 2 * G)
    (hgC : 2 * ρ + 2 * G * κ' + 2 * G ≤ gC) (hgC0 : 0 < gC)
    (hκC : κ' + 1 ≤ κC) (hκ'1 : 1 ≤ κ')
    {m : ℕ} (rep : Fin m → Fin a.C) (t₀ : ℝ) {q : Point}
    (h0 : (q.1, t₀) ∈ goodPath a γ u τ κ' lam) (hq : q ∈ goodPath a γ u τ κ' lam)
    (hnt : min ‖q2normal a (tagOf a γ hC (q.1, t₀)) - q2normal a (tagOf a γ hC q)‖
            ‖q2normal a (tagOf a γ hC (q.1, t₀)) + q2normal a (tagOf a γ hC q)‖ ≤ g * H)
    {i : Fin m} (hbin : q2bin a Kc G (tagOf a γ hC (q.1, t₀)) = q2bin a Kc G (rep i))
    (hnat : NativeLine p k γ κC q.1) :
    q ∈ cF a γ t₀ lam Kc G gC κC (3 * G) (rep i) := by
  classical
  set b' := tagOf a γ hC (q.1, t₀) with hb'
  set b'' := tagOf a γ hC q with hb''
  set bi := rep i with hbi
  obtain ⟨htag', hF', hlong'⟩ := goodPath_tag a γ hc hdisj hC h0
  obtain ⟨htag'', hF'', hlong''⟩ := goodPath_tag a γ hc hdisj hC hq
  have hy0 : ‖y q.1 0‖ ≤ κ' := by have := hq.2.2.2.2; linarith [norm_nonneg (v q.1)]
  have hv0 : ‖v q.1‖ ≤ κ' := by have := hq.2.2.2.2; linarith [norm_nonneg (y q.1 0)]
  -- strip coefficients of the two tags along the same line
  have hi' := goodPath_intercept hc hdisj hC hρ hKc h0
  have hi'' := goodPath_intercept hc hdisj hC hρ hKc hq
  have hs' := goodPath_speed hc hdisj hC hρ hKc h0
  have hs'' := goodPath_speed hc hdisj hC hρ hKc hq
  rw [← hb'] at hi' hs'
  rw [← hb''] at hi'' hs''
  obtain ⟨hn0, hn1, hint, hsp⟩ := q2bin_eq_close hG hbin
  have hnb : ‖q2normal a b' - q2normal a bi‖ ≤ 2 * G := norm_sub_le_of_bin hn0 hn1
  -- compatibility of the later tag with the representative
  have hcompat : Compat a Kc (3 * G) b'' bi := by
    rcases min_le_iff.1 hnt with hpar | hanti
    · left
      refine ⟨?_, ?_, ?_⟩
      · calc ‖q2normal a b'' - q2normal a bi‖
            = ‖(q2normal a b' - q2normal a bi) - (q2normal a b' - q2normal a b'')‖ := by
              congr 1; abel
          _ ≤ ‖q2normal a b' - q2normal a bi‖ + ‖q2normal a b' - q2normal a b''‖ := norm_sub_le _ _
          _ ≤ 2 * G + G := add_le_add hnb (hpar.trans hθG)
          _ = 3 * G := by ring
      · have hc1 := coeff_close hi' hi'' hpar hy0 hθ0
        calc |q2intercept a Kc b'' - q2intercept a Kc bi|
            = |(q2intercept a Kc b' - q2intercept a Kc bi) -
                (q2intercept a Kc b' - q2intercept a Kc b'')| := by ring_nf
          _ ≤ |q2intercept a Kc b' - q2intercept a Kc bi| +
                |q2intercept a Kc b' - q2intercept a Kc b''| := abs_sub _ _
          _ ≤ 3 * G := by linarith
      · have hc1 := coeff_close hs' hs'' hpar hv0 hθ0
        calc |q2speed a Kc b'' - q2speed a Kc bi|
            = |(q2speed a Kc b' - q2speed a Kc bi) - (q2speed a Kc b' - q2speed a Kc b'')| := by
              ring_nf
          _ ≤ |q2speed a Kc b' - q2speed a Kc bi| + |q2speed a Kc b' - q2speed a Kc b''| :=
              abs_sub _ _
          _ ≤ 3 * G := by linarith
    · right
      refine ⟨?_, ?_, ?_⟩
      · calc ‖q2normal a b'' + q2normal a bi‖
            = ‖(q2normal a b' + q2normal a b'') - (q2normal a b' - q2normal a bi)‖ := by
              congr 1; abel
          _ ≤ ‖q2normal a b' + q2normal a b''‖ + ‖q2normal a b' - q2normal a bi‖ := norm_sub_le _ _
          _ ≤ G + 2 * G := add_le_add (hanti.trans hθG) hnb
          _ = 3 * G := by ring
      · have hc1 := coeff_close_neg hi' hi'' hanti hy0 hθ0
        calc |q2intercept a Kc b'' + q2intercept a Kc bi|
            = |(q2intercept a Kc b' + q2intercept a Kc b'') -
                (q2intercept a Kc b' - q2intercept a Kc bi)| := by ring_nf
          _ ≤ |q2intercept a Kc b' + q2intercept a Kc b''| +
                |q2intercept a Kc b' - q2intercept a Kc bi| := abs_sub _ _
          _ ≤ 3 * G := by linarith
      · have hc1 := coeff_close_neg hs' hs'' hanti hv0 hθ0
        calc |q2speed a Kc b'' + q2speed a Kc bi|
            = |(q2speed a Kc b' + q2speed a Kc b'') - (q2speed a Kc b' - q2speed a Kc bi)| := by
              ring_nf
          _ ≤ |q2speed a Kc b' + q2speed a Kc b''| + |q2speed a Kc b' - q2speed a Kc bi| :=
              abs_sub _ _
          _ ≤ 3 * G := by linarith
  -- the line is in the assignment of the full-time chart
  have hmate : b' ∈ binMates a γ t₀ lam Kc G bi := by
    simp only [binMates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨htag'.1, htag'.2.2, hlong', raw_intercept_le hc htag'.2.1 hρ hlong' hKc hy0,
      raw_speed_le hc htag'.2.1 hρ hlong' hKc hv0, hbin⟩
  have hy1 : ‖y q.1 1‖ ≤ κ' := by
    have heq : y q.1 1 = y q.1 0 + v q.1 := by
      have := y_sub_y q.1 0 1
      rw [sub_zero, one_smul] at this
      rw [← this]; abel
    rw [heq]
    calc ‖y q.1 0 + v q.1‖ ≤ ‖y q.1 0‖ + ‖v q.1‖ := norm_add_le _ _
      _ ≤ κ' := hq.2.2.2.2
  have hstripL : q.1 ∈ stripLines a γ t₀ lam Kc G κ' bi := by
    refine ⟨?_, hy0, hy1⟩
    simp only [Set.mem_iUnion, exists_prop]
    exact ⟨b', hmate, htag'.2.1⟩
  have hn : ‖q2normal a bi‖ = 1 := norm_minorNormal (hc.det_ne bi)
  have hfit : q.1.2 ∈ stripFit a γ Kc gC κC bi := by
    intro t ht
    have hyt : ‖y q.1 t‖ ≤ κ' := norm_y_le_of_ends q.1 ht hy0 hy1
    have hstrip := stripLines_strip hc hG hρ bi hstripL ht
    obtain ⟨n1, n2, n3⟩ := hnat t ht
    refine ⟨?_, ?_, n2, ?_⟩
    · have := stripFrame_line_bound hn hgC0 (q2intercept a Kc bi) (q2speed a Kc bi) t
        (y q.1 t) hyt (hstrip.trans hgC)
      exact this.trans hκC
    · rw [mul_one]; exact n1
    · rw [div_one]; exact n3
  -- assemble
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [mem_compatEvent]
    exact ⟨b'', mem_compatSet.2 ⟨htag''.1, hcompat⟩, hF''⟩
  · refine ⟨mem_cA.2 ⟨⟨b', hmate, htag'.2.1⟩, hfit⟩, ?_⟩
    have hsel := hc.selected b'' hF''
    rw [htag''.1] at hsel
    have ht := (hEsub hsel.1).2
    constructor
    · exact ht.1
    · linarith [ht.2]
  · show p.B k γ / κC ≤ |MvPolynomial.eval (x q.1 q.2) (MvPolynomial.pderiv 3 (p.P k γ))|
    have hnat' := hq.2.2.2.1.2.2.2
    refine le_trans ?_ hnat'
    exact div_le_div_of_nonneg_left hB.le (by linarith) (by linarith)

end

/-- **World mass of the full-time charts.** The retained mass of paired full-time
binning is at most the mass of the full-time charts plus the transverse mass at the
binning time. -/
theorem cF_world_mass (hp : Valid p) (a : Atlas p k) (γ : Fin (p.W k))
    {M D : ℕ} {κ r : ℝ} {ex : Fin a.C → Prop} (hc : ChartsHyp a M D κ r ex)
    (hdisj : ∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b'))
    (hC : 0 < a.C) {u τ κ' lam ρ Kc g H gC κC : ℝ} (hu : 0 < u) (huη : u ≤ p.η * p.L)
    (hρ : ∀ b, lam ≤ ‖longCol (a.Q b)‖ → minorWidth (a.Q b) * (κ * stripScale a.T) ≤ ρ)
    (hKc : κ' + ρ ≤ Kc) (hg : 0 < g) (hH : 1 ≤ H)
    (hρG : 2 * ρ + g * H * κ' ≤ 2 * (g * H ^ 2))
    (hgC : 2 * ρ + 2 * (g * H ^ 2) * κ' + 2 * (g * H ^ 2) ≤ gC) (hgC0 : 0 < gC)
    (hκC : κ' + 1 ≤ κC) (hκ'1 : 1 ≤ κ') (hK : p.K k ≤ κC)
    (t₀ : ℝ) {m : ℕ} (rep : Fin m → Fin a.C) (A : Fin m → Set Line)
    (L : Observation → Finset (Fin m))
    (hA : ∀ i, A i = {l | (l, t₀) ∈ goodPath a γ u τ κ' lam ∧
      q2bin a Kc (g * H ^ 2) (tagOf a γ hC (l, t₀)) = q2bin a Kc (g * H ^ 2) (rep i)})
    {X : ENNReal}
    (hret : X ≤ (((p.ν k γ).prod volume).restrict (goodPath a γ u τ κ' lam))
        {q | ∃ i, q.1 ∈ A i ∧ i ∈ L (obs (p.B k γ) (δ (p.N k) p.L) q)}) :
    X ≤ ((p.ν k γ).prod volume)
          (⋃ i, cF a γ t₀ lam Kc (g * H ^ 2) gC κC (3 * (g * H ^ 2)) (rep i)) +
        ((p.ν k γ).prod volume)
          {q | (q.1, t₀) ∈ goodPath a γ u τ κ' lam ∧ q ∈ goodPath a γ u τ κ' lam ∧
            g * H < min ‖q2normal a (tagOf a γ hC (q.1, t₀)) - q2normal a (tagOf a γ hC q)‖
              ‖q2normal a (tagOf a γ hC (q.1, t₀)) + q2normal a (tagOf a γ hC q)‖} := by
  classical
  obtain ⟨M', D', hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  have hEsub : p.E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 := ((hfmt k).2.2.2.1 γ).2.2.2.2.2.2.2.2.1
  have hB := hp.B_pos k γ
  have hG : 0 < g * H ^ 2 := by positivity
  have hθ0 : 0 ≤ g * H := by positivity
  have hθG : g * H ≤ g * H ^ 2 := by nlinarith
  have hgm := measurableSet_goodPath a γ (τ := τ) (κ' := κ') (lam := lam) hp hc hu huη
  rw [Measure.restrict_apply' hgm] at hret
  set μ := (p.ν k γ).prod (volume : Measure ℝ) with hμ
  set Bad := {q : Point | (q.1, t₀) ∈ goodPath a γ u τ κ' lam ∧ q ∈ goodPath a γ u τ κ' lam ∧
      g * H < min ‖q2normal a (tagOf a γ hC (q.1, t₀)) - q2normal a (tagOf a γ hC q)‖
        ‖q2normal a (tagOf a γ hC (q.1, t₀)) + q2normal a (tagOf a γ hC q)‖} with hBad
  set Null := {l : Line | ¬ NativeLine p k γ κC l} ×ˢ (Set.univ : Set ℝ) with hNull
  have hnull : μ Null = 0 := by
    rw [hμ, hNull, Measure.prod_prod]
    have : p.ν k γ {l : Line | ¬ NativeLine p k γ κC l} = 0 :=
      ae_iff.1 (ae_nativeLine hp k γ hK)
    rw [this, zero_mul]
  have hsub : {q : Point | ∃ i, q.1 ∈ A i ∧ i ∈ L (obs (p.B k γ) (δ (p.N k) p.L) q)} ∩
      goodPath a γ u τ κ' lam ⊆
      ((⋃ i, cF a γ t₀ lam Kc (g * H ^ 2) gC κC (3 * (g * H ^ 2)) (rep i)) ∪ Bad) ∪ Null := by
    rintro q ⟨⟨i, hqA, -⟩, hq⟩
    rw [hA i] at hqA
    obtain ⟨h0, hbin⟩ := hqA
    by_cases hnat : NativeLine p k γ κC q.1
    · by_cases htr : g * H < min ‖q2normal a (tagOf a γ hC (q.1, t₀)) - q2normal a (tagOf a γ hC q)‖
          ‖q2normal a (tagOf a γ hC (q.1, t₀)) + q2normal a (tagOf a γ hC q)‖
      · exact Or.inl (Or.inr ⟨h0, hq, htr⟩)
      · push Not at htr
        refine Or.inl (Or.inl (Set.mem_iUnion.2 ⟨i, ?_⟩))
        exact goodPair_mem_cF hc hdisj hEsub hB hC hρ hKc hG hθ0 hθG hρG hgC hgC0 hκC hκ'1
          rep t₀ h0 hq htr hbin hnat
    · exact Or.inr ⟨hnat, Set.mem_univ _⟩
  calc X ≤ μ ({q : Point | ∃ i, q.1 ∈ A i ∧ i ∈ L (obs (p.B k γ) (δ (p.N k) p.L) q)} ∩
          goodPath a γ u τ κ' lam) := hret
    _ ≤ μ (((⋃ i, cF a γ t₀ lam Kc (g * H ^ 2) gC κC (3 * (g * H ^ 2)) (rep i)) ∪ Bad) ∪
          Null) := measure_mono hsub
    _ ≤ μ ((⋃ i, cF a γ t₀ lam Kc (g * H ^ 2) gC κC (3 * (g * H ^ 2)) (rep i)) ∪ Bad) +
          μ Null := measure_union_le _ _
    _ ≤ μ (⋃ i, cF a γ t₀ lam Kc (g * H ^ 2) gC κC (3 * (g * H ^ 2)) (rep i)) + μ Bad := by
        rw [hnull, add_zero]; exact measure_union_le _ _

end

end Submission.Obl.k4_raw_localized_native_systems.C
