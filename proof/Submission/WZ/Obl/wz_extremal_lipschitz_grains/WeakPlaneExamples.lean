-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.WeakPlaneExamples.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.WeakPlaneMap

/-!
# Extremal examples with a weak plane map

Combining the incidence-regularized compact extremal examples (`compact_incidence_extremal_examples`)
with `weak_plane_map` (broad threshold `θ = δ^(σ/32)`, pair threshold `β = δ^(σ/64)`, Kakeya loss
`δ^(-σ/8)`) gives arbitrarily small compact extremal examples with a measurable unit normal map of
precision `δ^(σ/64)`: the formal analogue of sticky Lemma 4.3.
-/

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal

/-- The numerical condition of `weak_plane_map` for regularized extremal examples. -/
theorem weak_plane_numeric {σ ε C δ M : ℝ} {n : ℕ} (hε : 0 < ε) (hδ : 0 < δ) (hn : 0 < n)
    (hC : 0 < C) (hcut : δ ^ (σ / 8 - 7 * ε / 2) ≤ 1 / (20 * C))
    (hM : δ ^ ε * (n : ℝ) * δ ^ 2 ≤ M) :
    20 * C * (δ ^ (σ / 32)) ^ (-8:ℝ) * δ ^ (3 - σ / 8) * (n : ℝ) ^ (3/2:ℝ) *
        ((n : ℝ) * δ ^ (2 - σ - ε)) ≤
      ((n : ℝ) * δ ^ (2 - σ + ε)) ^ (3/2:ℝ) * M := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have e1 : ((n : ℝ) * δ ^ (2 - σ + ε)) ^ (3/2:ℝ) = (n : ℝ) ^ (3/2:ℝ) * δ ^ (3 - 3 * σ / 2 + 3 * ε / 2) := by
    rw [Real.mul_rpow hn'.le (by positivity), ← Real.rpow_mul hδ.le]
    congr 2; ring
  have e2 : (δ ^ (σ / 32)) ^ (-8:ℝ) = δ ^ (-(σ / 4)) := by
    rw [← Real.rpow_mul hδ.le]; congr 1; ring
  have e3 : δ ^ (-(σ / 4)) * δ ^ (3 - σ / 8) * δ ^ (2 - σ - ε) =
      δ ^ (σ / 8 - 7 * ε / 2) * (δ ^ (3 - 3 * σ / 2 + 3 * ε / 2) * (δ ^ ε * δ ^ 2)) := by
    rw [show (δ : ℝ) ^ (2:ℕ) = δ ^ (2:ℝ) by rw [Real.rpow_two]]
    simp only [← Real.rpow_add hδ]
    congr 1; ring
  have hX : 0 ≤ (n : ℝ) ^ (3/2:ℝ) * δ ^ (3 - 3 * σ / 2 + 3 * ε / 2) := by positivity
  have h20 : 20 * C * δ ^ (σ / 8 - 7 * ε / 2) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hcut (by positivity : (0:ℝ) ≤ 20 * C)
    rwa [mul_one_div_cancel (by positivity)] at this
  rw [e1, e2]
  calc 20 * C * δ ^ (-(σ / 4)) * δ ^ (3 - σ / 8) * (n : ℝ) ^ (3/2:ℝ) * ((n : ℝ) * δ ^ (2 - σ - ε))
      = (20 * C * δ ^ (σ / 8 - 7 * ε / 2)) *
          ((n : ℝ) ^ (3/2:ℝ) * δ ^ (3 - 3 * σ / 2 + 3 * ε / 2) * (δ ^ ε * (n : ℝ) * δ ^ 2)) := by
        have := e3
        calc _ = 20 * C * (n : ℝ) ^ (3/2:ℝ) * (n : ℝ) *
              (δ ^ (-(σ / 4)) * δ ^ (3 - σ / 8) * δ ^ (2 - σ - ε)) := by ring
          _ = _ := by rw [this]; ring
    _ ≤ 1 * ((n : ℝ) ^ (3/2:ℝ) * δ ^ (3 - 3 * σ / 2 + 3 * ε / 2) * M) := by
        gcongr
    _ = _ := by ring


/-- **Extremal examples with a weak plane map.**  At a positive optimal exponent `σ`, there are
arbitrarily small compact extremal examples (same `Family`, `Separated` and volume bounds as in
`Grains`) carrying a measurable unit normal map with `|⟪v i, P p⟫| ≤ δ^(σ/64)` on every
shading. -/
theorem weak_plane_examples {σ : ℝ} (hσ : 0 < σ)
    (hbelow : ∀ t : ℝ, t < σ → Examples t) (habove : ∀ t : ℝ, σ < t → ¬ Examples t)
    (η d0 : ℝ) (hη : 0 < η) (hd0 : 0 < d0) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ d0 ∧ δ ≤ (1 / 100 : ℝ) ∧
      ∃ (n : ℕ) (x v : Fin n → Space) (Y : Fin n → Set Space),
        Family η δ n x v Y ∧ Separated η δ n x v ∧ (∀ i, IsCompact (Y i)) ∧
        volume (⋃ i, Y i) ≤ ENNReal.ofReal (δ ^ (σ - η)) ∧
        ∃ P : Space → Space, Measurable P ∧ (∀ p ∈ ⋃ i, Y i, ‖P p‖ = 1) ∧
          ∀ i p, p ∈ Y i → |inner ℝ (v i) (P p)| ≤ δ ^ (σ / 64) := by
  obtain ⟨C, hC, hwp⟩ := weak_plane_map (σ / 8) (by positivity)
  set ε := min (η / 4) (σ / 64) with hεdef
  have hε : 0 < ε := lt_min (by positivity) (by positivity)
  have hεη : ε ≤ η / 4 := min_le_left _ _
  have hεσ : ε ≤ σ / 64 := min_le_right _ _
  obtain ⟨d1, hd1, hcut1⟩ := exists_power_cutoff (a := σ / 8 - 7 * ε / 2)
    (by linarith) (by positivity : (0:ℝ) < 1 / (20 * C))
  obtain ⟨d2, hd2, hcut2⟩ := exists_power_cutoff (a := ε) hε (by norm_num : (0:ℝ) < 1 / 8)
  obtain ⟨d3, hd3, hcut3⟩ := exists_power_cutoff (a := η - 2 * ε) (by linarith)
    (by norm_num : (0:ℝ) < 1 / 2)
  obtain ⟨δ, hδ, hδ0, hδmax, n, x, v, Y, hH, hS, hYc, hV, hup, hlo⟩ :=
    compact_incidence_extremal_examples hbelow habove ε (min d0 (min d1 (min d2 d3))) hε
      (lt_min hd0 (lt_min hd1 (lt_min hd2 hd3)))
  have hδd0 : δ ≤ d0 := hδ0.trans (min_le_left _ _)
  have hδd1 : δ ≤ d1 := hδ0.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδd2 : δ ≤ d2 := hδ0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hδd3 : δ ≤ d3 := hδ0.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_right _ _)))
  have hδ1 : δ ≤ 1 := by linarith
  have hn : 0 < n := hH.1
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hYm : ∀ i, MeasurableSet (Y i) := hH.2.2.2.2.1
  have hYT : ∀ i, Y i ⊆ tube δ (x i) (v i) := hH.2.2.2.2.2.1
  have hv : ∀ i, ‖v i‖ = 1 := hH.2.1
  have hmass := hH.mass_lower hδ
  obtain ⟨Z, P, hZY, hZm, hZmass, hPm, hPn, hPi⟩ :=
    hwp (δ ^ (σ / 32)) (δ ^ (σ / 64)) δ ((n : ℝ) * δ ^ (2 - σ + ε)) ((n : ℝ) * δ ^ (2 - σ - ε))
      (by positivity) (Real.rpow_le_one hδ.le hδ1 (by positivity)) (by positivity) hδ hδ1
      (by positivity) n x v Y hv hYm hYT hH.union_subset_ball
      (fun p hp => ⟨(hlo p hp).le, hup p⟩)
      (weak_plane_numeric hε hδ hn hC (hcut1 δ hδ hδd1) hmass)
  -- the refined family
  have hZfam : Family (2 * ε) δ n x v Z := by
    refine hH.of_subsets_mass hZY hZm ?_
    have h8 : δ ^ (2 * ε) ≤ δ ^ ε / 8 := by
      have := hcut2 δ hδ hδd2
      calc δ ^ (2 * ε) = δ ^ ε * δ ^ ε := by rw [← Real.rpow_add hδ]; ring_nf
        _ ≤ δ ^ ε * (1 / 8) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = δ ^ ε / 8 := by ring
    calc δ ^ (2 * ε) * (n : ℝ) * δ ^ 2 ≤ δ ^ ε / 8 * (n : ℝ) * δ ^ 2 := by gcongr
      _ = (δ ^ ε * (n : ℝ) * δ ^ 2) / 8 := by ring
      _ ≤ shadingMass Y / 8 := by gcongr
      _ ≤ shadingMass Z := hZmass
  have hp : δ ^ η ≤ δ ^ (2 * ε) / 2 := by
    have := hcut3 δ hδ hδd3
    calc δ ^ η = δ ^ (2 * ε) * δ ^ (η - 2 * ε) := by rw [← Real.rpow_add hδ]; ring_nf
      _ ≤ δ ^ (2 * ε) * (1 / 2) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = δ ^ (2 * ε) / 2 := by ring
  obtain ⟨W, hWZ, hWc, hWfam⟩ := hZfam.compact_refinement hp
  have hWY : ∀ i, W i ⊆ Y i := fun i => (hWZ i).trans (hZY i)
  refine ⟨δ, hδ, hδd0, hδmax, n, x, v, W, hWfam, hS.mono_error hδ hδ1 (by linarith), hWc, ?_,
    P, hPm, ?_, ?_⟩
  · refine (measure_mono (iUnion_mono hWY)).trans (hV.trans ?_)
    exact ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith))
  · intro p hp
    exact hPn p (iUnion_mono hWZ hp)
  · intro i p hp
    have h := hPi i p (hWZ i hp)
    have e : max (δ ^ (σ / 32) / δ ^ (σ / 64)) (δ ^ (σ / 64)) = δ ^ (σ / 64) := by
      have : δ ^ (σ / 32) / δ ^ (σ / 64) = δ ^ (σ / 64) := by
        rw [← Real.rpow_sub hδ]; ring_nf
      rw [this, max_self]
    rwa [e] at h

end WangZahlLot.Obl.wz_extremal_lipschitz_grains

/-- Frozen-style form of `weak_plane_examples` (Mathlib terms only), suitable as a child
statement: a positive optimal exponent has arbitrarily small compact extremal examples with a
measurable unit plane map of precision `δ^(σ/64)`. -/
theorem WangZahlLot.Obl.wz_extremal_lipschitz_grains.weak_plane_child : (fun (T:ℝ→(EuclideanSpace ℝ (Fin 3))→(EuclideanSpace ℝ (Fin 3))→Set (EuclideanSpace ℝ (Fin 3)))=>(fun (H:ℝ→ℝ→(n:ℕ)→(Fin n→(EuclideanSpace ℝ (Fin 3)))→(Fin n→(EuclideanSpace ℝ (Fin 3)))→(Fin n→Set (EuclideanSpace ℝ (Fin 3)))→Prop)=>(fun (D:ℝ→(EuclideanSpace ℝ (Fin 3))→(EuclideanSpace ℝ (Fin 3))→Set (EuclideanSpace ℝ (Fin 3)))=>(fun (S:ℝ→ℝ→(n:ℕ)→(Fin n→(EuclideanSpace ℝ (Fin 3)))→(Fin n→(EuclideanSpace ℝ (Fin 3)))→Prop)=>(fun (X:ℝ→Prop)=>(fun (W:ℝ→Prop)=>∀σ:ℝ,0<σ→(∀t:ℝ,t<σ→X t)→(∀t:ℝ,σ<t→¬X t)→W σ) (fun (σ:ℝ)=>∀η d0:ℝ,0<η→0<d0→∃δ:ℝ,0<δ∧δ≤d0∧δ≤(1/100:ℝ)∧∃(n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3))) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3))),H η δ n x v Y∧S η δ n x v∧(∀i,IsCompact (Y i))∧MeasureTheory.volume (⋃ i,Y i)≤ENNReal.ofReal (δ^(σ-η))∧∃(P:(EuclideanSpace ℝ (Fin 3))→(EuclideanSpace ℝ (Fin 3))),Measurable P∧(∀p,p ∈ (⋃ i,Y i)→‖P p‖=1)∧(∀i p,p ∈ Y i→|inner ℝ (v i) (P p)|≤δ^(σ/64)))) (fun (s:ℝ)=>∀η d0:ℝ,0<η→0<d0→∃δ:ℝ,0<δ∧δ≤d0∧δ≤(1/100:ℝ)∧∃(n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3))) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3))),H η δ n x v Y∧S η δ n x v∧MeasureTheory.volume (⋃ i,Y i)≤ENNReal.ofReal (δ^s))) (fun (η δ:ℝ) (n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3)))=>∀r:ℝ,δ≤r→ r≤1→∃ρ:ℝ,r≤ρ∧ρ≤1∧ρ≤δ^(-η)*r∧∃k:ℕ,0<k∧∃z w:Fin k→(EuclideanSpace ℝ (Fin 3)),(∀j,‖w j‖=1)∧(∀j j',j≠j'→MeasureTheory.volume (T ρ (z j) (w j)∩T ρ (z j') (w j'))≤(1/2:ENNReal)*MeasureTheory.volume (T ρ (z j) (w j)))∧(∀i,∃! j,T δ (x i) (v i)⊆T ρ (z j) (w j))∧(∀j,∃i,T δ (x i) (v i)⊆T ρ (z j) (w j))∧(∀j j',(Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j) (w j)}:ℝ)≤δ^(-η)*(Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j') (w j')}:ℝ))∧(∀j,∀W:Set (EuclideanSpace ℝ (Fin 3)),Convex ℝ W→ENNReal.ofReal ((Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j) (w j)∧T δ (x i) (v i)⊆W}:ℝ)*ρ^2)≤ENNReal.ofReal (δ^(-η)*(Set.ncard {i|T δ (x i) (v i)⊆T ρ (z j) (w j)}:ℝ))*MeasureTheory.volume W)∧(∀i j j',T δ (x i) (v i)⊆D ρ (z j) (w j)→T δ (x i) (v i)⊆D ρ (z j') (w j')→j=j'))) (fun (ρ:ℝ) (z w:(EuclideanSpace ℝ (Fin 3)))=>Metric.thickening (10*ρ) (segment ℝ (z-(9/2:ℝ) • w) (z+(11/2:ℝ) • w)))) (fun (η δ:ℝ) (n:ℕ) (x v:Fin n→(EuclideanSpace ℝ (Fin 3))) (Y:Fin n→Set (EuclideanSpace ℝ (Fin 3)))=>0<n∧(∀i,‖v i‖=1)∧(∀i,T δ (x i) (v i)⊆Metric.ball 0 1)∧(∀i j,i≠j→MeasureTheory.volume (T δ (x i) (v i)∩T δ (x j) (v j))≤(1/2:ENNReal)*MeasureTheory.volume (T δ (x i) (v i)))∧(∀i,MeasurableSet (Y i))∧(∀i,Y i⊆T δ (x i) (v i))∧ENNReal.ofReal (δ^η*(n:ℝ)*δ^2)≤Finset.sum Finset.univ (fun i=>MeasureTheory.volume (Y i)))) (fun (δ:ℝ) (x v:(EuclideanSpace ℝ (Fin 3)))=>Metric.thickening δ (segment ℝ x (x+v))) := by
  change ∀ σ : ℝ, 0 < σ →
    (∀ t : ℝ, t < σ → WangZahlLot.Obl.wz_extremal_lipschitz_grains.Examples t) →
    (∀ t : ℝ, σ < t → ¬WangZahlLot.Obl.wz_extremal_lipschitz_grains.Examples t) → _
  intro σ hσ hbelow habove η d0 hη hd0
  exact WangZahlLot.Obl.wz_extremal_lipschitz_grains.weak_plane_examples hσ hbelow habove η d0 hη hd0
