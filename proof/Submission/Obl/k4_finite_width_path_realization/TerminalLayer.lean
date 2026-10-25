import Submission.Obl.k4_finite_width_path_realization.Forests
import Submission.Obl.k4_finite_width_path_realization.Toolkit.ExclusionGuards

namespace Submission.Obl.k4_finite_width_path_realization

open MeasureTheory Filter

noncomputable def Forest.layerLabels {p : Data} {k : ℕ} (a : Forest p k) (i : ℕ) :
    Finset (Fin a.C) := by
  classical
  exact Finset.univ.filter (fun b => a.lev b = i)

theorem Forest.layerLabels_mem {p : Data} {k : ℕ} (a : Forest p k) (i : ℕ)
    (b : Fin a.C) : b ∈ a.layerLabels i ↔ a.lev b = i := by
  classical
  simp [Forest.layerLabels]

noncomputable def Forest.terminalLayer {p : Data} {k M D m : ℕ}
    (a : Forest p k) (r : ℕ → ℝ) (ha : a.Core M D m r) (hm : 0 < m) : Atlas p k where
  κ := a.κ
  T := a.T (m - 1)
  C := (a.layerLabels (m - 1)).card
  γ := fun b => a.γ ((a.layerLabels (m - 1)).orderEmbOfFin rfl b)
  j := fun b => ⟨a.j ((a.layerLabels (m - 1)).orderEmbOfFin rfl b), by
    have hlev := (a.layerLabels_mem _ _).mp
      ((a.layerLabels (m - 1)).orderEmbOfFin_mem rfl b)
    have hj := (ha.2.2.2.2.2 ((a.layerLabels (m - 1)).orderEmbOfFin rfl b)).2.1
    rwa [hlev] at hj⟩
  c := fun b => a.c ((a.layerLabels (m - 1)).orderEmbOfFin rfl b)
  u := fun b => a.u ((a.layerLabels (m - 1)).orderEmbOfFin rfl b)
  Q := fun b => a.Q ((a.layerLabels (m - 1)).orderEmbOfFin rfl b)
  R := fun b => a.R ((a.layerLabels (m - 1)).orderEmbOfFin rfl b)
  A := fun b => a.A ((a.layerLabels (m - 1)).orderEmbOfFin rfl b)
  F := fun b => a.F ((a.layerLabels (m - 1)).orderEmbOfFin rfl b)

theorem Forest.terminalLayer_mass {p : Data} {k M D m : ℕ}
    (a : Forest p k) (r : ℕ → ℝ) (ha : a.Core M D m r) (hm : 0 < m) :
    (a.terminalLayer r ha hm).mass = a.layerMass (m - 1) := by
  classical
  unfold Atlas.mass Forest.terminalLayer Forest.layerMass Forest.mass
  calc
    _ = ∑ b ∈ Finset.univ.image ((a.layerLabels (m - 1)).orderEmbOfFin rfl),
        ENNReal.ofReal (p.ω k (a.γ b)) * ((p.ν k (a.γ b)).prod volume) (a.F b) := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => ((a.layerLabels (m - 1)).orderEmbOfFin rfl).injective h
    _ = _ := by
      rw [(a.layerLabels (m - 1)).image_orderEmbOfFin_univ rfl]
      simp only [Forest.layerLabels, Finset.sum_filter]

theorem Forest.terminalLayer_true {p : Data} {k M D m : ℕ}
    (a : Forest p k) (r : ℕ → ℝ) (ha : a.Core M D m r) (hm : 0 < m)
    (hr : r (m - 1) = p.L) : (a.terminalLayer r ha hm).TrueAt M D p.L := by
  classical
  let s := a.layerLabels (m - 1)
  let e := s.orderEmbOfFin rfl
  have he (b) : a.lev (e b) = m - 1 :=
    (a.layerLabels_mem _ _).mp (s.orderEmbOfFin_mem rfl b)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact le_trans (by exact_mod_cast (le_trans (Finset.card_le_univ s) (by simp))) ha.2.2.1
  · intro b b' hne hγ hj
    apply ha.2.2.2.2.1 (e b) (e b') (fun h => hne (e.injective h))
      ((he b).trans (he b').symm) hγ
    exact congrArg Fin.val hj
  · intro b
    have hc := (ha.2.2.2.2.2 (e b)).2.2.1
    simpa only [Forest.terminalLayer, he b, hr] using hc
  · rw [Forest.terminalLayer_mass]
    exact ha.2.2.2.1 _ (by omega)

/-- A finite-format terminal guard bounds the common final width of a forest. -/
theorem terminal_width_bound {p : Data} (hp : p.Valid) {M D m : ℕ}
    (hm : 0 < m) {h w : ℝ} (hnt : ¬ NarrowTerminal p h w) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ᶠ k in atTop, ∀ (a : Forest p k) (r nw : ℕ → ℝ)
      (ε : ℝ), a.Core M D m r → r (m - 1) = p.L →
      a.κ ≤ p.N k ^ τ → (2 : ℝ) ^ a.T (m - 1) ≤ p.N k ^ h →
      (∀ b, p.N k ^ (-a.width b) = |Matrix.det (a.Q b)| * (4 : ℝ) ^ a.T (a.lev b)) →
      (∀ b, |a.width b - nw (a.lev b)| ≤ ε) → nw (m - 1) < w + ε := by
  obtain ⟨τ, hτ, hguard⟩ := finite_narrowness_atlas_guard hp hnt M D
  refine ⟨τ, hτ, hguard.mono fun k hk a r nw ε ha hr hκ hT hwidth hbin => ?_⟩
  let b := a.terminalLayer r ha hm
  have hN : 1 ≤ p.N k := by linarith [hp.N_ge k]
  obtain ⟨z, hz⟩ := hk b ha.1 ha.2.1 hκ
    (hT.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)))
    (a.terminalLayer_true r ha hm hr)
  let e := (a.layerLabels (m - 1)).orderEmbOfFin rfl
  have he : a.lev (e z) = m - 1 :=
    (a.layerLabels_mem _ _).mp ((a.layerLabels (m - 1)).orderEmbOfFin_mem rfl z)
  have hww := hwidth (e z)
  have hbb := (abs_le.mp (hbin (e z))).1
  rw [he] at hww hbb
  have hstrict : -w + τ < -a.width (e z) := by
    apply (Real.rpow_lt_rpow_left_iff (by linarith [hp.N_ge k] : 1 < p.N k)).mp
    rw [hww]
    exact hz
  linarith

end Submission.Obl.k4_finite_width_path_realization
