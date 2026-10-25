import Mathlib
import ChallengeDeps
import Submission.Obl.k4_scalar_marked_packet_recovery.Assembly
import Submission.Obl.k4_scalar_marked_packet_recovery.Geometry
import Submission.Obl.k4_profile_density_bounds.Asymptotics
set_option linter.unusedVariables false

open Set MeasureTheory Filter
open Submission.Obl.k4_scalar_marked_packet_recovery

/-!
# `Submission.k4_scalar_marked_packet_recovery`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_scalar_marked_packet_recovery`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_scalar_marked_packet_recovery/`
belong to this obligation.
-/

theorem Submission.k4_scalar_marked_packet_recovery : ((fun (Subpower : ∀ (_N _K : ℕ → ℝ), Prop) => ((fun (Noise : ∀ (_σ : ℝ), MeasureTheory.Measure (Fin 5 → ℝ)) => ((fun (MarkedPrior : ∀ (_σ : ℝ) (_H : ℕ) (_b₀ : Fin _H → Fin 5 → ℝ) (_w : Fin _H → ℝ), MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) => ((fun (MarkedEvent : ∀ (_H _J : ℕ) (_mark : Fin _H → Fin _J → Bool), Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) => ((fun (MarkedLaw : ∀ (_σ : ℝ) (_H _J : ℕ) (_b₀ : Fin _H → Fin 5 → ℝ) (_w : Fin _H → ℝ) (_mark : Fin _H → Fin _J → Bool), MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) => ((fun (Tables : ∀ (_N _K _m : ℝ) (_M _H _J : ℕ) (_b₀ : Fin _H → Fin 5 → ℝ) (_w : Fin _H → ℝ) (_mark : Fin _H → Fin _J → Bool), Prop) => ((fun (Coupling : ∀ (_N _K _s _m : ℝ) (_α : Type) [MeasurableSpace _α] (_ν : MeasureTheory.Measure _α) (_μ : MeasureTheory.Measure (_α × ℝ)) (_b : _α → Fin 5 → ℝ) (_H _J : ℕ) (_tag : _α → Fin _H) (_b₀ : Fin _H → Fin 5 → ℝ) (_w : Fin _H → ℝ) (_mark : Fin _H → Fin _J → Bool), Prop) => ((fun (NoisyOutput : ∀ (_N _d _s _m _c _ε : ℝ) (_angular : Bool) (_μ : MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)), Prop) => ((fun (BlockOutput : ∀ (_N _d _s _m _c _ε : ℝ) (_angular : Bool) (_α : Type) [MeasurableSpace _α] (_μ : MeasureTheory.Measure (_α × ℝ)) (_b : _α → Fin 5 → ℝ), Prop) => ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Filter.Tendsto N Filter.atTop Filter.atTop → Subpower N K → ∀ d s m : ℝ, 0 ≤ d → d < 1 → 0 < s → s < m → ∀ (α : ℕ → Type) [∀ k, MeasurableSpace (α k)] (ν : (k : ℕ) → MeasureTheory.Measure (α k)) (μ : (k : ℕ) → MeasureTheory.Measure (α k × ℝ)) (b : (k : ℕ) → α k → Fin 5 → ℝ) (c : ℕ → ℝ) (angular : ℕ → Bool), ∀ (M : ℕ) (H J : ℕ → ℕ) (b₀ : (k : ℕ) → Fin (H k) → Fin 5 → ℝ) (w : (k : ℕ) → Fin (H k) → ℝ) (mark : (k : ℕ) → Fin (H k) → Fin (J k) → Bool) (tag : (k : ℕ) → α k → Fin (H k)), (∀ k, Tables (N k) (K k) m M (H k) (J k) (b₀ k) (w k) (mark k)) → (∀ k, Coupling (N k) (K k) s m (α k) (ν k) (μ k) (b k) (H k) (J k) (tag k) (b₀ k) (w k) (mark k)) → (∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, NoisyOutput (N k) d s m (c k) ε (angular k) (MarkedLaw (N k ^ (-m)) (H k) (J k) (b₀ k) (w k) (mark k))) → ∀ ε : ℝ, 0 < ε → ∃ᶠ k in Filter.atTop, BlockOutput (N k) d s m (c k) ε (angular k) (α k) (μ k) (b k)) (fun (N d s m c ε : ℝ) (angular : Bool) (α : Type) [MeasurableSpace α] (μ : MeasureTheory.Measure (α × ℝ)) (b : α → Fin 5 → ℝ) => (((fun (y : α → ℝ → ℝ) => ((fun (x : α → ℝ → ℝ) => ∃ (n : ℕ) (β t₀ q : ℝ) (A : Fin n → Set α) (u v : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ), N ^ (-ε) ≤ q ∧ 0 ≤ t₀ ∧ t₀ + q ≤ 1 ∧ N ^ (-m) / N ^ ε ≤ β ∧ β ≤ N ^ ε ∧ (angular = true → N ^ (-ε) ≤ β) ∧ (∀ i, MeasurableSet (A i)) ∧ (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, |u i| + |v i| ≤ N ^ ε ∧ (P i).totalDegree ≤ 2 ∧ (∀ t ∈ Set.Icc t₀ (t₀ + q), ∀ w ∈ Set.Icc (-1 : ℝ) 1, |MvPolynomial.eval ![t, u i + t * v i + β * w] (P i)| ≤ N ^ ε) ∧ (∀ l ∈ A i, ∀ t ∈ Set.Icc t₀ (t₀ + q), |y l t - u i - t * v i| ≤ N ^ ε * β ∧ |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤ N ^ ε * N ^ (-s)) ∧ ENNReal.ofReal (c * (N ^ (-s)) ^ d * β / N ^ ε) ≤ μ (A i ×ˢ Set.Icc (0 : ℝ) 1)) ∧ ENNReal.ofReal (N ^ (-ε)) ≤ μ {p | ∃ i, p.1 ∈ A i}) (fun l t => b l 2 + t * b l 3 + t ^ 2 * b l 4))) (fun l t => b l 0 + t * b l 1)))))) (fun (N d s m c ε : ℝ) (angular : Bool) (μ : MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) => (((fun (y : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) => ((fun (x : (ℕ × (Fin 5 → ℝ)) → ℝ → ℝ) => ∃ (n : ℕ) (β t₀ q : ℝ) (A : Fin n → Set (ℕ × (Fin 5 → ℝ))) (u v : Fin n → ℝ) (P : Fin n → MvPolynomial (Fin 2) ℝ), N ^ (-ε) ≤ q ∧ 0 ≤ t₀ ∧ t₀ + q ≤ 1 ∧ N ^ (-m) / N ^ ε ≤ β ∧ β ≤ N ^ ε ∧ (angular = true → N ^ (-ε) ≤ β) ∧ (∀ i, MeasurableSet (A i)) ∧ (∀ i j, i ≠ j → Disjoint (A i) (A j)) ∧ (∀ i, |u i| + |v i| ≤ N ^ ε ∧ (P i).totalDegree ≤ 2 ∧ (∀ t ∈ Set.Icc t₀ (t₀ + q), ∀ w ∈ Set.Icc (-1 : ℝ) 1, |MvPolynomial.eval ![t, u i + t * v i + β * w] (P i)| ≤ N ^ ε) ∧ (∀ l ∈ A i, ∀ t ∈ Set.Icc t₀ (t₀ + q), |y l t - u i - t * v i| ≤ N ^ ε * β ∧ |x l t - MvPolynomial.eval ![t, y l t] (P i)| ≤ N ^ ε * N ^ (-s)) ∧ ENNReal.ofReal (q * c * (N ^ (-s)) ^ d * β / N ^ ε) ≤ μ (A i ×ˢ Set.Icc t₀ (t₀ + q))) ∧ ENNReal.ofReal (N ^ (-ε)) ≤ μ {p | (∃ i, p.1 ∈ A i) ∧ p.2 ∈ Set.Icc t₀ (t₀ + q)}) (fun (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4))) (fun (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) => l.2 0 + t * l.2 1)))))) (fun (N K s m : ℝ) (α : Type) [MeasurableSpace α] (ν : MeasureTheory.Measure α) (μ : MeasureTheory.Measure (α × ℝ)) (b : α → Fin 5 → ℝ) (H J : ℕ) (tag : α → Fin H) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) => (Measurable tag ∧ (∀ j, ENNReal.ofReal (w j) = ν {l | tag l = j}) ∧ (∀ l e, |b l e - b₀ (tag l) e| ≤ N ^ (-10 * (m + s + 1))) ∧ (∀ j z, mark j z = true → ENNReal.ofReal (w j / ((J : ℝ) * K)) ≤ μ {p | tag p.1 = j ∧ p.2 ∈ Set.Ico ((z : ℝ) / (J : ℝ)) (((z : ℝ) + 1) / (J : ℝ))}))))) (fun (N K m : ℝ) (M H J : ℕ) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) => (1 ≤ J ∧ (H : ℝ) ≤ N ^ (M : ℝ) ∧ (J : ℝ) ≤ N ^ (M : ℝ) ∧ 1 ≤ (J : ℝ) * N ^ (-m) ∧ (J : ℝ) * N ^ (-m) ≤ 2 ∧ (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧ (∀ j e, |b₀ j e| ≤ K) ∧ ENNReal.ofReal (K⁻¹) ≤ MarkedLaw (N ^ (-m)) H J b₀ w mark Set.univ)))) (fun (σ : ℝ) (H J : ℕ) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) => (((MarkedPrior σ H b₀ w).prod MeasureTheory.volume).restrict (MarkedEvent H J mark))))) (fun (H J : ℕ) (mark : Fin H → Fin J → Bool) => ({p | ∃ j : Fin H, p.1.1 = (j : ℕ) ∧ ∃ z : Fin J, mark j z = true ∧ p.2 ∈ Set.Ico ((z : ℝ) / (J : ℝ)) (((z : ℝ) + 1) / (J : ℝ))})))) (fun (σ : ℝ) (H : ℕ) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) => (∑ j, ENNReal.ofReal (w j) • MeasureTheory.Measure.map (fun u : Fin 5 → ℝ => ((j : ℕ), b₀ j + u)) (Noise σ))))) (fun (σ : ℝ) => (MeasureTheory.Measure.pi (fun _ : Fin 5 => ENNReal.ofReal (σ⁻¹) • MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) σ)))))) (fun (N K : ℕ → ℝ) => ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε))) := by
  classical
  intro N K hN hNt hK d s m hd hd1 hs hsm α instα ν μ b c angular M H J b₀ w mark tag
    hTables hCouple hnoisy ε hε
  change Subpower N K at hK
  change (∀ k, Tables (N k) (K k) m M (H k) (J k) (b₀ k) (w k) (mark k)) at hTables
  change (∀ k, Coupling (N k) (K k) s m (α k) (ν k) (μ k) (b k)
    (H k) (J k) (tag k) (b₀ k) (w k) (mark k)) at hCouple
  change (∀ δ : ℝ, 0 < δ → ∃ᶠ k in atTop, NoisyOutput (N k) d s m (c k) δ
    (angular k) (MarkedLaw (N k ^ (-m)) (H k) (J k) (b₀ k) (w k) (mark k))) at hnoisy
  change ∃ᶠ k in atTop, BlockOutput (N k) d s m (c k) ε (angular k) (α k) (μ k) (b k)
  let η := min (ε / 100) (1 / 100)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηeps : η < ε := by have := min_le_left (ε / 100) (1 / 100); dsimp [η]; linarith
  have hη1 : η ≤ 1 := by have := min_le_right (ε / 100) (1 / 100); dsimp [η]; linarith
  have hηgap : 3 * η < ε := by have := min_le_left (ε / 100) (1 / 100); dsimp [η]; linarith
  have hN1 : ∀ k, 1 ≤ N k := fun k => by linarith [hN k]
  have hgapEvent := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN1 hNt hK.1 hK.2 1 hηgap (show (0 : ℝ) ≤ 4 by norm_num)
  have hgeomEvent := eventually_geometry_conditions N hN hNt hs hsm hη hηeps hη1
  refine ((hnoisy η hη).and_eventually (hgapEvent.and hgeomEvent)).mono ?_
  intro k hk
  obtain ⟨hout, hgap', hgeom1, hgeom2, hgeom3⟩ := hk
  have hp : (N k ^ η) ^ 3 = N k ^ (3 * η) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith [hN k])]
    congr 1
    norm_num
    ring
  have hgap : 4 * K k * (N k ^ η) ^ 3 ≤ N k ^ ε := by
    simpa only [pow_one, hp] using hgap'.le
  obtain ⟨n, β, t₀, q, A, u, v, P, hq, ht₀, htq, hβ, hβ', hang, hA, hdisj, hpacket, hmass⟩ := hout
  obtain ⟨hJ, hHbound, hJbound, hmesh0, hmesh1, hw, hw1, hb₀, hmarked⟩ := hTables k
  obtain ⟨htag, htagmass, hround, hmark⟩ := hCouple k
  refine recover_system (hN1 k) (by linarith [hK.1 k]) hη.le hηeps.le hgap
    (by omega) (μ k) (b k) (tag k) htag (b₀ k) (w k) hw hw1 (mark k) hmark
    (angular k) β t₀ q A hq ht₀ htq hβ hβ' hang hA hdisj ?_ hmass ?_
  · exact fun i => (hpacket i).2.2.2.2
  · intro jitter hjitter i
    obtain ⟨hL, hσ0, hσ1, hNs⟩ := base_facts (hN k) hs hsm hη.le
    have hg := geometry_transfer hσ0 hσ1 hjitter hβ ht₀ htq hL hNs hgeom1 hgeom2 hgeom3
      (hpacket i).1 (hpacket i).2.1 (hpacket i).2.2.1
    refine ⟨u i - jitter 0, v i - jitter 1, shiftPoly jitter (P i),
      hg.1, hg.2.1, hg.2.2.1, ?_⟩
    intro l hl t ht
    have hfit := (hpacket i).2.2.2.1 (embed (b₀ k) (tag k l) jitter) hl t ht
    exact hg.2.2.2 (b₀ k (tag k l)) (b k l) (hround l) t ht hfit.1 hfit.2
