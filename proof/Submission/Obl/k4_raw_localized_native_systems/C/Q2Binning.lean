import Submission.Obl.k4_raw_localized_native_systems.C.Q2TotalBad
import Submission.Obl.k4_raw_localized_native_systems.C.RecoveryInterface

/-
Adapted from this LOT tree, o178, session x0596, `Q2Binning.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

/-!
# Paired full-time binning applied to the good path of one world

All hypotheses of paired full-time binning (o175, `PairedFullTimeBinning`) are
verified for the good path of a later chart system in one world, except the
bad-pair estimate itself, which is supplied (for good worlds) by the total bound
of `Q2TotalBad`.  The conclusion is the full-time strip system `C` of the paper's
Proposition 10.2 in that world.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

variable {p : Data} {k : ℕ}

/-- The conclusion of paired full-time binning for one world. -/
def WorldStrips (a : Atlas p k) (γ : Fin (p.W k)) (hC : 0 < a.C) (u τ κ' lam Kc KB H g : ℝ)
    (CB : ℕ) : Prop :=
  ∃ (t₀ : ℝ) (m : ℕ) (rep : Fin m → Fin a.C) (A : Fin m → Set Line)
    (L : Observation → Finset (Fin m)),
    t₀ ∈ Set.Icc (0 : ℝ) 1 ∧ (m : ℝ) ≤ ((CB : ℝ) * KB / (g * H ^ 2)) ^ CB ∧
    (∀ i, A i = {l | (l, t₀) ∈ goodPath a γ u τ κ' lam ∧
      (fun i => ![⌊q2normal a i 0 / (g * H ^ 2)⌋, ⌊q2normal a i 1 / (g * H ^ 2)⌋,
        ⌊q2intercept a Kc i / (g * H ^ 2)⌋, ⌊q2speed a Kc i / (g * H ^ 2)⌋])
          (tagOf a γ hC (l, t₀)) =
      (fun i => ![⌊q2normal a i 0 / (g * H ^ 2)⌋, ⌊q2normal a i 1 / (g * H ^ 2)⌋,
        ⌊q2intercept a Kc i / (g * H ^ 2)⌋, ⌊q2speed a Kc i / (g * H ^ 2)⌋]) (rep i)}) ∧
    (∀ i, MeasurableSet (A i)) ∧ (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
    (∀ i l, l ∈ A i → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |inner ℝ (q2normal a (rep i)) (y l 0 + t • v l) - q2intercept a Kc (rep i) -
        t * q2speed a Kc (rep i)| ≤ (CB : ℝ) * KB * (g * H ^ 2)) ∧
    (∀ o, ((L o).card : ℝ) ≤ (CB : ℝ) * KB) ∧ (∀ i, MeasurableSet {o | i ∈ L o}) ∧
    ENNReal.ofReal ((((p.ν k γ).prod volume).restrict (goodPath a γ u τ κ' lam)).real Set.univ ^ 2 / 4) ≤
      (((p.ν k γ).prod volume).restrict (goodPath a γ u τ κ' lam))
        {q | ∃ i, q.1 ∈ A i ∧ i ∈ L (obs (p.B k γ) (δ (p.N k) p.L) q)}

/-- The four-entry bin of a chart's normal, intercept and speed. -/
def q2bin (a : Atlas p k) (Kc G : ℝ) (i : Fin a.C) : Fin 4 → ℤ :=
  ![⌊q2normal a i 0 / G⌋, ⌊q2normal a i 1 / G⌋, ⌊q2intercept a Kc i / G⌋, ⌊q2speed a Kc i / G⌋]

/-- The body of paired full-time binning (o175) for a fixed constant. -/
def B0At (C : ℕ) : Prop :=
  ∀ (α:Type) [MeasurableSpace α] (ν:MeasureTheory.Measure α) (E:Set (α × ℝ)) (b v:α→ EuclideanSpace ℝ (Fin 2)) (n:ℕ) (normal:Fin n→ EuclideanSpace ℝ (Fin 2)) (intercept speed:Fin n→ ℝ) (tag:α × ℝ→ Fin n) (O:α × ℝ→ EuclideanSpace ℝ (Fin 3) × ℤ) (lst:(EuclideanSpace ℝ (Fin 3) × ℤ)→ Finset (Fin n)) (K H g:ℝ),MeasureTheory.IsProbabilityMeasure ν→ MeasurableSet E→ E ⊆ Set.univ ×ˢ Set.Icc (0:ℝ) 1→ Measurable b→ Measurable v→ Measurable tag→ Measurable O→ (∀ i,‖normal i‖ = 1∧ |intercept i| + |speed i| ≤ K)→ (∀ o,((lst o).card:ℝ) ≤ K)→ (∀ i,MeasurableSet {o | i ∈ lst o})→ (∀ p ∈ E,tag p ∈ lst (O p)∧‖b p.1‖ + ‖v p.1‖ ≤ K∧ |inner ℝ (normal (tag p)) (b p.1) - intercept (tag p)| ≤ K * g∧ |inner ℝ (normal (tag p)) (v p.1) - speed (tag p)| ≤ K * g)→ 2 ≤ K→ (C:ℝ) * K ^ 2 ≤ H→ 0 < g→ g * H ^ 2 ≤ 1→ (fun (μ:MeasureTheory.Measure (α × ℝ)) (pair:MeasureTheory.Measure (α × (ℝ × ℝ))) (bin:Fin n→ Fin 4→ ℤ) => 0 < μ Set.univ→ pair {p | (p.1,p.2.1) ∈ E∧(p.1,p.2.2) ∈ E∧g * H < min ‖normal (tag (p.1,p.2.1)) - normal (tag (p.1,p.2.2))‖ ‖normal (tag (p.1,p.2.1)) + normal (tag (p.1,p.2.2))‖} ≤ ENNReal.ofReal ((μ.real Set.univ) ^ 2 / 4)→ ∃ (t₀:ℝ) (m:ℕ) (rep:Fin m→ Fin n) (A:Fin m→ Set α) (L:(EuclideanSpace ℝ (Fin 3) × ℤ)→ Finset (Fin m)),t₀ ∈ Set.Icc (0:ℝ) 1∧(m:ℝ) ≤ ((C:ℝ) * K / (g * H ^ 2)) ^ C∧Function.Injective (fun i => bin (rep i))∧(∀ i,A i = {l | (l,t₀) ∈ E∧bin (tag (l,t₀)) = bin (rep i)})∧(∀ i,MeasurableSet (A i))∧(∀ i j,i ≠ j→ Disjoint (A i) (A j))∧(∀ i l,l ∈ A i→ ∀ t ∈ Set.Icc (0:ℝ) 1,|inner ℝ (normal (rep i)) (b l + t • v l) - intercept (rep i) - t * speed (rep i)| ≤ (C:ℝ) * K * (g * H ^ 2))∧(∀ o,((L o).card:ℝ) ≤ (C:ℝ) * K)∧(∀ i,MeasurableSet {o | i ∈ L o})∧ENNReal.ofReal ((μ.real Set.univ) ^ 2 / 4) ≤ μ {p | ∃ i,p.1 ∈ A i∧i ∈ L (O p)}) ((ν.prod MeasureTheory.volume).restrict E) (ν.prod (MeasureTheory.volume.prod MeasureTheory.volume)) (fun i => ![⌊normal i 0 / (g * H ^ 2)⌋,⌊normal i 1 / (g * H ^ 2)⌋,⌊intercept i / (g * H ^ 2)⌋,⌊speed i / (g * H ^ 2)⌋])

theorem exists_b0At (hB : PairedFullTimeBinning) : ∃ C : ℕ, 2 ≤ C ∧ B0At C := hB

/-- **Paired full-time binning in one world.** -/
theorem q2_world_strips {CB : ℕ} (hCB2 : 2 ≤ CB) (hB : B0At CB) :
    ∀ (hp : Valid p) (a : Atlas p k) (γ : Fin (p.W k)) {M D : ℕ} {κ r : ℝ}
      {ex : Fin a.C → Prop} (hc : ChartsHyp a M D κ r ex)
      (hdisj : ∀ b b', b ≠ b' → a.γ b = a.γ b' → a.j b = a.j b' → Disjoint (a.A b) (a.A b'))
      (hknown : ∀ b, ∀ z ∈ a.F b, b ∈ a.lst (a.γ b) (obs (p.B k (a.γ b)) (δ (p.N k) p.L) z))
      (κL : ℕ) (hcard : ∀ o, (a.lst γ o).card ≤ κL)
      (hmeas : ∀ b, MeasurableSet {o | b ∈ a.lst γ o})
      (hC : 0 < a.C) {u τ κ' lam ρ Kc KB g H : ℝ} (hu : 0 < u) (huη : u ≤ p.η * p.L)
      (hρ : ∀ b, lam ≤ ‖longCol (a.Q b)‖ → minorWidth (a.Q b) * (κ * stripScale a.T) ≤ ρ) (hKc : κ' + ρ ≤ Kc)
      (hKcB : 2 * Kc ≤ KB) (hκLB : (κL : ℝ) ≤ KB) (hκ'B : κ' ≤ KB) (hρB : ρ ≤ KB * g)
      (hK2 : 2 ≤ KB) (hg : 0 < g) (hgH : g * H ^ 2 ≤ 1) (hHB : (CB : ℝ) * KB ^ 2 ≤ H)
      (hρ0 : 0 ≤ ρ) (hκ'0 : 0 ≤ κ')
      (hpos : 0 < (((p.ν k γ).prod volume).restrict (goodPath a γ u τ κ' lam)) Set.univ)
      (hbad : ((p.ν k γ).prod (volume.prod volume))
          {z | (z.1, z.2.1) ∈ goodPath a γ u τ κ' lam ∧ (z.1, z.2.2) ∈ goodPath a γ u τ κ' lam ∧
            g * H < min ‖q2normal a (tagOf a γ hC (z.1, z.2.1)) -
                q2normal a (tagOf a γ hC (z.1, z.2.2))‖
              ‖q2normal a (tagOf a γ hC (z.1, z.2.1)) +
                q2normal a (tagOf a γ hC (z.1, z.2.2))‖} ≤
        ENNReal.ofReal ((((p.ν k γ).prod volume).restrict
          (goodPath a γ u τ κ' lam)).real Set.univ ^ 2 / 4)),
      ∃ (t₀ : ℝ) (m : ℕ) (rep : Fin m → Fin a.C) (A : Fin m → Set Line)
        (L : Observation → Finset (Fin m)),
        t₀ ∈ Set.Icc (0 : ℝ) 1 ∧ (m : ℝ) ≤ ((CB : ℝ) * KB / (g * H ^ 2)) ^ CB ∧
        Function.Injective (fun i => q2bin a Kc (g * H ^ 2) (rep i)) ∧
        (∀ i, A i = {l | (l, t₀) ∈ goodPath a γ u τ κ' lam ∧
          q2bin a Kc (g * H ^ 2) (tagOf a γ hC (l, t₀)) = q2bin a Kc (g * H ^ 2) (rep i)}) ∧
        (∀ i, MeasurableSet (A i)) ∧ (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧
        (∀ i l, l ∈ A i → ∀ t ∈ Set.Icc (0 : ℝ) 1,
          |inner ℝ (q2normal a (rep i)) (y l 0 + t • v l) - q2intercept a Kc (rep i) -
            t * q2speed a Kc (rep i)| ≤ (CB : ℝ) * KB * (g * H ^ 2)) ∧
        (∀ o, ((L o).card : ℝ) ≤ (CB : ℝ) * KB) ∧ (∀ i, MeasurableSet {o | i ∈ L o}) ∧
        ENNReal.ofReal ((((p.ν k γ).prod volume).restrict
            (goodPath a γ u τ κ' lam)).real Set.univ ^ 2 / 4) ≤
          (((p.ν k γ).prod volume).restrict (goodPath a γ u τ κ' lam))
            {q | ∃ i, q.1 ∈ A i ∧ i ∈ L (obs (p.B k γ) (δ (p.N k) p.L) q)} := by
  have hCB := hB
  intro hp a γ M D κ r ex hc hdisj hknown κL hcard hmeas hC u τ κ' lam ρ Kc KB g H hu huη hρ hKc
    hKcB hκLB hκ'B hρB hK2 hg hgH hHB hρ0 hκ'0 hpos hbad
  obtain ⟨M', D', hfmt⟩ := hp.2.2.2.2.2.2.2.2.1
  haveI : IsProbabilityMeasure (p.ν k γ) := ((hfmt k).2.2.2.1 γ).1
  have hEm := measurableSet_goodPath a γ (τ := τ) (κ' := κ') (lam := lam) hp hc hu huη
  have hKc0 : 0 ≤ Kc := by linarith
  have hbm : Measurable (fun l : Line => y l 0) := by unfold y x; fun_prop
  have hsub : goodPath a γ u τ κ' lam ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 := by
    intro q hq
    obtain ⟨htag, hF, hlong⟩ := goodPath_tag a γ hc hdisj hC hq
    have hsel := hc.selected _ hF
    rw [htag.1] at hsel
    exact ((hfmt k).2.2.2.1 γ).2.2.2.2.2.2.2.2.1 hsel.1
  have hnorm : ∀ i, ‖q2normal a i‖ = 1 ∧ |q2intercept a Kc i| + |q2speed a Kc i| ≤ KB := by
    intro i
    refine ⟨norm_minorNormal (hc.det_ne i), ?_⟩
    have h1 : |q2intercept a Kc i| ≤ Kc := abs_clip_le hKc0
    have h2 : |q2speed a Kc i| ≤ Kc := abs_clip_le hKc0
    linarith
  have hpath : ∀ q ∈ goodPath a γ u τ κ' lam, tagOf a γ hC q ∈ a.lst γ (obs (p.B k γ) (δ (p.N k) p.L) q) ∧
      ‖y q.1 0‖ + ‖v q.1‖ ≤ KB ∧
      |inner ℝ (q2normal a (tagOf a γ hC q)) (y q.1 0) - q2intercept a Kc (tagOf a γ hC q)| ≤
        KB * g ∧
      |inner ℝ (q2normal a (tagOf a γ hC q)) (v q.1) - q2speed a Kc (tagOf a γ hC q)| ≤ KB * g := by
    intro q hq
    obtain ⟨htag, hF, hlong⟩ := goodPath_tag a γ hc hdisj hC hq
    refine ⟨?_, hq.2.2.2.2.trans hκ'B, ?_, ?_⟩
    · have := hknown _ q hF
      rwa [htag.1] at this
    · exact (goodPath_intercept hc hdisj hC hρ hKc hq).trans hρB
    · exact (goodPath_speed hc hdisj hC hρ hKc hq).trans hρB
  have hres := hCB Line (p.ν k γ) (goodPath a γ u τ κ' lam) (fun l => y l 0) v a.C (q2normal a)
    (q2intercept a Kc) (q2speed a Kc) (tagOf a γ hC) (obs (p.B k γ) (δ (p.N k) p.L)) (a.lst γ)
    KB H g inferInstance hEm hsub hbm measurable_v' (measurable_tagOf a γ hC hc.measA)
    (measurable_obs' _ _) hnorm (fun o => (Nat.cast_le.2 (hcard o)).trans hκLB) hmeas hpath
    hK2 hHB hg hgH hpos hbad
  exact hres
end

end Submission.Obl.k4_raw_localized_native_systems.C
