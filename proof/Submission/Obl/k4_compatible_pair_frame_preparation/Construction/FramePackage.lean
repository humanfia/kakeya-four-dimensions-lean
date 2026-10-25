-- Adapted from this LOT tree, o206, session x0753, commit f0f3bdbb,
-- Submission/Obl/k4_coarse_pair_frame_preparation/Construction/FramePackage.lean.
-- Earlier attribution comments are retained below.

-- Adapted from this LOT tree, o104, session x0472, commit 1aecc7d,
-- Submission/Obl/k4_terminal_time_extension/FramePackage.lean.
-- Earlier source attributions in the original file are preserved below.

import Submission.Obl.k4_compatible_pair_frame_preparation.Construction.FrameBounds

/-!
# The common frames of one sample

Old charts `b` (world `γ₀ b`, old block `j₀ b` of length `2^-(T+s)`, chart `(c₀ b, u₀ b, Q₀ b)`)
in one dyadic scale class (`R₁ ≤ r₁ ≤ 2R₁`, `r₂ ≤ 2R₂`) get the frame key
`(world, coarse block, chartCode)` on the coarse blocks of length `2^-T`.  The frames are
the finite image of the keys (`frameKeys`), at most one per old chart.

* `frame_confinement_key`: a trajectory confined in an old chart on its old block is
  confined (slack 2) in the frame of its key on the whole coarse block.
* `frameQ_key_bounds`: the frame matrices satisfy `det ≠ 0`, the entry bound
  `Σ|Q| ≤ κ / 2^T` with `κ = 632 κ₀²`, and polynomial inverse-entry bounds.
* `compatKeys`: the frame keys listed by a witness chart, at most `98 (2Kb+1)^4`;
  `srcKey_mem_compatKeys`: the source's key is listed by every witness chart sharing a
  trajectory, world and coarse block, unless the normals are separated by more than `g`.
-/

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Construction

open Matrix Submission.Lib.K4VelocityStrips

/-- The coarse block containing an old block. -/
def coarseIdx {T s : ℕ} (j : Fin (2 ^ (T + s))) : Fin (2 ^ T) :=
  ⟨(j : ℕ) / 2 ^ s, by
    have h : (j : ℕ) < 2 ^ s * 2 ^ T := by
      have h0 := j.2
      have e : 2 ^ (T + s) = 2 ^ s * 2 ^ T := by rw [pow_add, Nat.mul_comm]
      omega
    exact Nat.div_lt_of_lt_mul h⟩

theorem coarseIdx_bounds {T s : ℕ} (j : Fin (2 ^ (T + s))) :
    ((coarseIdx j : ℕ) : ℝ) / 2 ^ T ≤ (j : ℝ) / 2 ^ (T + s) ∧
    ((j : ℝ) + 1) / 2 ^ (T + s) ≤ ((coarseIdx j : ℕ) + 1 : ℝ) / 2 ^ T := by
  have hs : (0 : ℝ) < 2 ^ s := by positivity
  have hT : (0 : ℝ) < 2 ^ T := by positivity
  have h1 : (j : ℕ) / 2 ^ s * 2 ^ s ≤ (j : ℕ) := Nat.div_mul_le_self _ _
  have h2 : (j : ℕ) < ((j : ℕ) / 2 ^ s + 1) * 2 ^ s := by
    have := Nat.lt_div_mul_add (a := (j : ℕ)) (b := 2 ^ s) (by positivity)
    linarith
  have r1 : (((j : ℕ) / 2 ^ s : ℕ) : ℝ) * 2 ^ s ≤ (j : ℝ) := by exact_mod_cast h1
  have r2 : (j : ℝ) + 1 ≤ ((((j : ℕ) / 2 ^ s : ℕ) : ℝ) + 1) * 2 ^ s := by
    have : (j : ℕ) + 1 ≤ ((j : ℕ) / 2 ^ s + 1) * 2 ^ s := h2
    exact_mod_cast this
  have e : (2 : ℝ) ^ (T + s) = 2 ^ T * 2 ^ s := pow_add _ _ _
  simp only [coarseIdx]
  constructor
  · rw [e, div_le_div_iff₀ hT (by positivity)]
    nlinarith
  · rw [e, div_le_div_iff₀ (by positivity) hT]
    nlinarith

/-- The midpoint of a coarse block. -/
noncomputable def tmid (T : ℕ) (J : Fin (2 ^ T)) : ℝ := ((J : ℕ) + 1 / 2 : ℝ) / 2 ^ T

/-- The frame key type. -/
abbrev FrKey (W T : ℕ) := Fin W × Fin (2 ^ T) × FrameCode

section Package

variable {W C₀ T s : ℕ} (γ₀ : Fin C₀ → Fin W) (j₀ : Fin C₀ → Fin (2 ^ (T + s)))
  (c₀ u₀ : Fin C₀ → EuclideanSpace ℝ (Fin 2)) (Q₀ : Fin C₀ → Matrix (Fin 2) (Fin 2) ℝ)
  (g S₁ S₂ A : ℝ)

/-- The frame key of an old chart. -/
noncomputable def srcKey (b : Fin C₀) : FrKey W T :=
  (γ₀ b, coarseIdx (j₀ b),
    chartCode g S₁ S₂ (1 / 2 ^ T) (tmid T (coarseIdx (j₀ b))) (c₀ b) (u₀ b) (Q₀ b))

/-- The frames: the keys of the old charts. -/
noncomputable def frameKeys : Finset (FrKey W T) := by
  classical
  exact Finset.univ.image (srcKey γ₀ j₀ c₀ u₀ Q₀ g S₁ S₂)

theorem srcKey_mem (b : Fin C₀) : srcKey γ₀ j₀ c₀ u₀ Q₀ g S₁ S₂ b ∈ frameKeys γ₀ j₀ c₀ u₀ Q₀ g S₁ S₂ := by
  classical
  unfold frameKeys
  exact Finset.mem_image_of_mem _ (Finset.mem_univ b)

theorem frameKeys_card_le : (frameKeys (T := T) γ₀ j₀ c₀ u₀ Q₀ g S₁ S₂).card ≤ C₀ := by
  classical
  unfold frameKeys
  exact Finset.card_image_le.trans (by simp)

theorem exists_src_of_mem {k : FrKey W T} (hk : k ∈ frameKeys γ₀ j₀ c₀ u₀ Q₀ g S₁ S₂) :
    ∃ b, srcKey γ₀ j₀ c₀ u₀ Q₀ g S₁ S₂ b = k := by
  classical
  unfold frameKeys at hk
  obtain ⟨b, -, hb⟩ := Finset.mem_image.mp hk
  exact ⟨b, hb⟩

/-- Frame data of a key. -/
noncomputable def keyC (k : FrKey W T) : EuclideanSpace ℝ (Fin 2) :=
  frameC g S₁ S₂ (1 / 2 ^ T) (tmid T k.2.1) k.2.2

noncomputable def keyU (k : FrKey W T) : EuclideanSpace ℝ (Fin 2) :=
  frameU g S₁ S₂ (1 / 2 ^ T) k.2.2

noncomputable def keyQ (k : FrKey W T) : Matrix (Fin 2) (Fin 2) ℝ :=
  frameQ g S₁ S₂ A k.2.2

/-- The witness list of an old chart. -/
noncomputable def compatKeys (Kb : ℕ) (b' : Fin C₀) : Finset (FrKey W T) := by
  classical
  exact (frameKeys γ₀ j₀ c₀ u₀ Q₀ g S₁ S₂).filter (fun k => k.1 = γ₀ b' ∧
    k.2.1 = coarseIdx (j₀ b') ∧
    k.2.2 ∈ codeNbhd g S₁ S₂ (1 / 2 ^ T) (tmid T (coarseIdx (j₀ b'))) (c₀ b') (u₀ b') (Q₀ b') Kb)

theorem compatKeys_card_le (Kb : ℕ) (b' : Fin C₀) :
    (compatKeys (T := T) γ₀ j₀ c₀ u₀ Q₀ g S₁ S₂ Kb b').card ≤ 98 * (2 * Kb + 1) ^ 4 := by
  classical
  refine le_trans ?_ (codeNbhd_card_le g S₁ S₂ (1 / 2 ^ T) (tmid T (coarseIdx (j₀ b')))
    (c₀ b') (u₀ b') (Q₀ b') Kb)
  apply Finset.card_le_card_of_injOn (fun k => k.2.2)
  · intro k hk
    unfold compatKeys at hk
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hk
    exact hk.2.2.2
  · intro k hk k' hk' h
    unfold compatKeys at hk hk'
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at hk hk'
    simp only at h
    obtain ⟨k1, k2, k3⟩ := k
    obtain ⟨k1', k2', k3'⟩ := k'
    simp only at hk hk' h
    rw [hk.2.1, hk'.2.1, hk.2.2.1, hk'.2.2.1, h]

end Package

/-! ### The properties of the frames -/

section Props

variable {W C₀ T s : ℕ} {γ₀ : Fin C₀ → Fin W} {j₀ : Fin C₀ → Fin (2 ^ (T + s))}
  {c₀ u₀ : Fin C₀ → EuclideanSpace ℝ (Fin 2)} {Q₀ : Fin C₀ → Matrix (Fin 2) (Fin 2) ℝ}
  {g R₁ R₂ κ₀ : ℝ}

/-- Confinement of a trajectory on its old block, as in the frozen chart. -/
def OldConfined (j₀ : Fin (2 ^ (T + s))) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (κ₀ : ℝ) (l : ℕ × (Fin 6 → ℝ)) : Prop :=
  ∀ t ∈ Set.Icc ((j₀ : ℝ) / 2 ^ (T + s)) (((j₀ : ℝ) + 1) / 2 ^ (T + s)),
    ‖Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)‖ ≤ κ₀

theorem oldConfined_ends {j : Fin (2 ^ (T + s))} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {l : ℕ × (Fin 6 → ℝ)} (h : OldConfined j c u Q κ₀ l) :
    ‖Matrix.toEuclideanLin Q⁻¹ (y l ((j : ℝ) / 2 ^ (T + s)) - c - ((j : ℝ) / 2 ^ (T + s)) • u)‖ ≤ κ₀ ∧
    ‖Matrix.toEuclideanLin Q⁻¹ (y l ((j : ℝ) / 2 ^ (T + s) + 1 / 2 ^ (T + s)) - c -
      ((j : ℝ) / 2 ^ (T + s) + 1 / 2 ^ (T + s)) • u)‖ ≤ κ₀ := by
  have hp : (0 : ℝ) < 2 ^ (T + s) := by positivity
  have e : (j : ℝ) / 2 ^ (T + s) + 1 / 2 ^ (T + s) = ((j : ℝ) + 1) / 2 ^ (T + s) := by
    rw [add_div]
  have hle : (j : ℝ) / 2 ^ (T + s) ≤ ((j : ℝ) + 1) / 2 ^ (T + s) := by gcongr; linarith
  rw [e]
  exact ⟨h _ ⟨le_rfl, hle⟩, h _ ⟨hle, le_rfl⟩⟩

theorem tmid_close {J : Fin (2 ^ T)} {t : ℝ}
    (ht : t ∈ Set.Icc ((J : ℝ) / 2 ^ T) (((J : ℝ) + 1) / 2 ^ T)) :
    |t - tmid T J| ≤ (1 / 2 ^ T) / 2 := by
  have hT : (0 : ℝ) < 2 ^ T := by positivity
  unfold tmid
  rw [abs_le]
  obtain ⟨h1, h2⟩ := ht
  constructor
  · have : ((J : ℕ) + 1 / 2 : ℝ) / 2 ^ T - 1 / 2 ^ T / 2 = (J : ℝ) / 2 ^ T := by
      field_simp; ring
    linarith
  · have : ((J : ℕ) + 1 / 2 : ℝ) / 2 ^ T + 1 / 2 ^ T / 2 = ((J : ℝ) + 1) / 2 ^ T := by
      field_simp; ring
    linarith

/-- The old block start lies in its coarse block, hence close to the midpoint. -/
theorem old_start_close (j : Fin (2 ^ (T + s))) :
    |tmid T (coarseIdx j) - (j : ℝ) / 2 ^ (T + s)| ≤ 1 / 2 ^ T := by
  obtain ⟨h1, h2⟩ := coarseIdx_bounds j
  have hp : (0 : ℝ) < 2 ^ (T + s) := by positivity
  have hmem : (j : ℝ) / 2 ^ (T + s) ∈ Set.Icc (((coarseIdx j : ℕ) : ℝ) / 2 ^ T)
      ((((coarseIdx j : ℕ) : ℝ) + 1) / 2 ^ T) := by
    refine ⟨h1, le_trans ?_ h2⟩
    gcongr; linarith
  have := tmid_close hmem
  rw [abs_sub_comm]
  have hT : (0 : ℝ) < 1 / 2 ^ T := by positivity
  linarith

theorem q_ratio : (1 : ℝ) / 2 ^ T = 2 ^ s * (1 / 2 ^ (T + s)) := by
  rw [pow_add]; field_simp

/-- **Whole-block confinement in the frame of the key.** -/
theorem frame_confinement_key (hg : 0 < g) (hg8 : g ≤ 1 / 8) (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (hκ₀ : 0 ≤ κ₀) (b : Fin C₀) (hQ : (Q₀ b).det ≠ 0)
    (hr₁ : r₁ (Q₀ b) ≤ 2 * R₁) (hr₂ : r₂ (Q₀ b) ≤ 2 * R₂) {l : ℕ × (Fin 6 → ℝ)}
    (hl : OldConfined (j₀ b) (c₀ b) (u₀ b) (Q₀ b) κ₀ l) {t : ℝ}
    (ht : t ∈ Set.Icc (((coarseIdx (j₀ b) : ℕ) : ℝ) / 2 ^ T)
      ((((coarseIdx (j₀ b) : ℕ) : ℝ) + 1) / 2 ^ T)) :
    ‖Matrix.toEuclideanLin (keyQ g (2 ^ s * R₁) (2 ^ s * max R₂ (g * R₁)) (2 * (78 * κ₀) + 2)
        (srcKey γ₀ j₀ c₀ u₀ Q₀ g (2 ^ s * R₁) (2 ^ s * max R₂ (g * R₁)) b))⁻¹
      (y l t - keyC g (2 ^ s * R₁) (2 ^ s * max R₂ (g * R₁))
          (srcKey γ₀ j₀ c₀ u₀ Q₀ g (2 ^ s * R₁) (2 ^ s * max R₂ (g * R₁)) b) -
        t • keyU g (2 ^ s * R₁) (2 ^ s * max R₂ (g * R₁))
          (srcKey γ₀ j₀ c₀ u₀ Q₀ g (2 ^ s * R₁) (2 ^ s * max R₂ (g * R₁)) b))‖ ≤ 2 := by
  have hq₀ : (0 : ℝ) < 1 / 2 ^ (T + s) := by positivity
  obtain ⟨h₁, h₂⟩ := oldConfined_ends hl
  obtain ⟨hA₁, hA₂⟩ := homogenized_scales (s := s) hg.le hq₀ hκ₀ hr₁ hr₂
  rw [← q_ratio] at hA₁ hA₂
  have hA₂' : κ₀ * (1 + 2 * (1 / 2 ^ T) / (1 / 2 ^ (T + s))) * r₂ (Q₀ b) +
      4 * g * (2 * (κ₀ * (1 + 2 * (1 / 2 ^ T) / (1 / 2 ^ (T + s)))) * r₁ (Q₀ b)) ≤
      78 * κ₀ * (2 ^ s * max R₂ (g * R₁)) := by
    refine le_trans ?_ hA₂
    have h0 : 0 ≤ 2 * (κ₀ * (1 + 2 * (1 / 2 ^ T) / (1 / 2 ^ (T + s)))) * r₁ (Q₀ b) := by
      have := r₁_nonneg (Q₀ b); positivity
    have := mul_le_mul_of_nonneg_right (show 4 * g ≤ 6 * g by linarith) h0
    linarith
  have hS₁ : (0 : ℝ) < 2 ^ s * R₁ := by positivity
  have hS₂ : (0 : ℝ) < 2 ^ s * max R₂ (g * R₁) := by
    have : 0 < max R₂ (g * R₁) := lt_max_of_lt_left hR₂
    positivity
  exact frame_confinement hg hg8 hS₁ hS₂ hq₀ (by positivity) (by positivity) hQ h₁ h₂
    (tmid_close ht) (old_start_close (j₀ b)) hA₁ hA₂'

/-- **Witness lists.**  The source's key is listed by a witness chart sharing a trajectory,
world and coarse block, unless their normals are separated by more than `g`. -/
theorem srcKey_mem_compatKeys (hg : 0 < g) (hg8 : g ≤ 1 / 8) (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (hκ₀ : 0 ≤ κ₀) {b b' : Fin C₀} (hγ : γ₀ b = γ₀ b')
    (hJ : coarseIdx (j₀ b) = coarseIdx (j₀ b'))
    (hQ : (Q₀ b).det ≠ 0) (hQ' : (Q₀ b').det ≠ 0)
    (hr₁ : r₁ (Q₀ b) ≤ 2 * R₁) (hr₂ : r₂ (Q₀ b) ≤ 2 * R₂)
    (hr₁' : r₁ (Q₀ b') ≤ 2 * R₁) (hr₂' : r₂ (Q₀ b') ≤ 2 * R₂) {l : ℕ × (Fin 6 → ℝ)}
    (hl : OldConfined (j₀ b) (c₀ b) (u₀ b) (Q₀ b) κ₀ l)
    (hl' : OldConfined (j₀ b') (c₀ b') (u₀ b') (Q₀ b') κ₀ l)
    (hwedge : |stripWedge (nrm (Q₀ b)) (nrm (Q₀ b'))| ≤ g)
    {Kb : ℕ} (hKb : 2 * (78 * κ₀) + 1 ≤ (Kb : ℝ)) :
    srcKey γ₀ j₀ c₀ u₀ Q₀ g (2 ^ s * R₁) (2 ^ s * max R₂ (g * R₁)) b ∈
      compatKeys γ₀ j₀ c₀ u₀ Q₀ g (2 ^ s * R₁) (2 ^ s * max R₂ (g * R₁)) Kb b' := by
  classical
  have hq₀ : (0 : ℝ) < 1 / 2 ^ (T + s) := by positivity
  obtain ⟨h₁, h₂⟩ := oldConfined_ends hl
  obtain ⟨h₁', h₂'⟩ := oldConfined_ends hl'
  obtain ⟨hA₁, hA₂⟩ := homogenized_scales (s := s) hg.le hq₀ hκ₀ hr₁ hr₂
  obtain ⟨hA₁', hA₂'⟩ := homogenized_scales (s := s) hg.le hq₀ hκ₀ hr₁' hr₂'
  rw [← q_ratio] at hA₁ hA₂ hA₁' hA₂'
  have hS₁ : (0 : ℝ) < 2 ^ s * R₁ := by positivity
  have hS₂ : (0 : ℝ) < 2 ^ s * max R₂ (g * R₁) := by
    have : 0 < max R₂ (g * R₁) := lt_max_of_lt_left hR₂
    positivity
  unfold compatKeys
  rw [Finset.mem_filter]
  refine ⟨srcKey_mem _ _ _ _ _ _ _ _ b, hγ, hJ, ?_⟩
  change chartCode g _ _ (1 / 2 ^ T) (tmid T (coarseIdx (j₀ b))) (c₀ b) (u₀ b) (Q₀ b) ∈ _
  rw [hJ]
  have htm := old_start_close (T := T) (j₀ b)
  have htm' := old_start_close (T := T) (j₀ b')
  rw [hJ] at htm
  exact chartCode_mem_codeNbhd hg hg8 hS₁ hS₂ hq₀ (by positivity) hQ hQ' h₁ h₂ h₁' h₂'
    htm htm' hA₁ hA₂ hA₁' hA₂' hwedge hKb

/-- **Frame matrix bounds.**  For an old chart in the scale class, with the frozen entry
bound `Σ|Q₀| ≤ κ₀ / 2^(T+s)`, its frame matrix is invertible with entry sum at most
`632 κ₀² / 2^T` and inverse-entry sum at most `4 A S₁ + 4 / (A S₂)`. -/
theorem frameQ_key_bounds (hg : 0 < g) (hg1 : g ≤ 1) (hg8 : g ≤ 1 / 8) (hR₁ : 0 < R₁)
    (hR₂ : 0 < R₂) (hR : R₂ ≤ R₁) (hκ₀ : 1 ≤ κ₀) (b : Fin C₀) (hQ : (Q₀ b).det ≠ 0)
    (hR₁b : R₁ ≤ r₁ (Q₀ b))
    (hsum : (∑ i : Fin 2, ∑ j : Fin 2, |Q₀ b i j|) ≤ κ₀ / 2 ^ (T + s)) :
    (keyQ g (2 ^ s * R₁) (2 ^ s * max R₂ (g * R₁)) (2 * (78 * κ₀) + 2)
        (srcKey γ₀ j₀ c₀ u₀ Q₀ g (2 ^ s * R₁) (2 ^ s * max R₂ (g * R₁)) b)).det ≠ 0 ∧
    |(keyQ g (2 ^ s * R₁) (2 ^ s * max R₂ (g * R₁)) (2 * (78 * κ₀) + 2)
        (srcKey γ₀ j₀ c₀ u₀ Q₀ g (2 ^ s * R₁) (2 ^ s * max R₂ (g * R₁)) b)).det| =
      ((2 * (78 * κ₀) + 2) * (2 ^ s * R₁)) * ((2 * (78 * κ₀) + 2) * (2 ^ s * max R₂ (g * R₁))) ∧
    (∑ i : Fin 2, ∑ j : Fin 2, |keyQ g (2 ^ s * R₁) (2 ^ s * max R₂ (g * R₁)) (2 * (78 * κ₀) + 2)
        (srcKey γ₀ j₀ c₀ u₀ Q₀ g (2 ^ s * R₁) (2 ^ s * max R₂ (g * R₁)) b) i j|) ≤
      (632 * κ₀ ^ 2) / 2 ^ T ∧
    (∑ i : Fin 2, ∑ j : Fin 2,
      (|keyQ g (2 ^ s * R₁) (2 ^ s * max R₂ (g * R₁)) (2 * (78 * κ₀) + 2)
        (srcKey γ₀ j₀ c₀ u₀ Q₀ g (2 ^ s * R₁) (2 ^ s * max R₂ (g * R₁)) b) i j| +
       |(keyQ g (2 ^ s * R₁) (2 ^ s * max R₂ (g * R₁)) (2 * (78 * κ₀) + 2)
        (srcKey γ₀ j₀ c₀ u₀ Q₀ g (2 ^ s * R₁) (2 ^ s * max R₂ (g * R₁)) b))⁻¹ i j|)) ≤
      4 * ((632 * κ₀ ^ 2) / 2 ^ T) + 4 / ((2 * (78 * κ₀) + 2) * (2 ^ s * max R₂ (g * R₁))) := by
  set A := 2 * (78 * κ₀) + 2 with hA
  set S₁ := (2 : ℝ) ^ s * R₁ with hS₁d
  set S₂ := (2 : ℝ) ^ s * max R₂ (g * R₁) with hS₂d
  have hS₁ : 0 < S₁ := by positivity
  have hm : 0 < max R₂ (g * R₁) := lt_max_of_lt_left hR₂
  have hS₂ : 0 < S₂ := by positivity
  have hApos : 0 < A := by positivity
  have hk : 0 < ‖codeVec g (srcKey γ₀ j₀ c₀ u₀ Q₀ g S₁ S₂ b).2.2.kn‖ :=
    codeVec_ne_zero hg hg8 (norm_nrm hQ)
  obtain ⟨hdet, hne, hent, hbud⟩ := frameQ_bounds hk hS₁ hS₂ hApos
  have hS₂S₁ : S₂ ≤ S₁ := by
    rw [hS₂d, hS₁d]
    gcongr
    exact max_le hR (by nlinarith)
  -- S₁ ≤ κ₀ / 2^T
  have hS₁κ : S₁ ≤ κ₀ / 2 ^ T := by
    have h1 : R₁ ≤ κ₀ / 2 ^ (T + s) := hR₁b.trans ((r₁_le_entrySum _).trans hsum)
    rw [hS₁d]
    calc (2 : ℝ) ^ s * R₁ ≤ 2 ^ s * (κ₀ / 2 ^ (T + s)) := by gcongr
      _ = κ₀ / 2 ^ T := by rw [pow_add]; field_simp
  have hAκ : A ≤ 158 * κ₀ := by rw [hA]; linarith
  have hent' : (∑ i : Fin 2, ∑ j : Fin 2, |keyQ g S₁ S₂ A (srcKey γ₀ j₀ c₀ u₀ Q₀ g S₁ S₂ b) i j|) ≤
      (632 * κ₀ ^ 2) / 2 ^ T := by
    refine hent.trans ?_
    have h1 : 2 * (A * S₁ + A * S₂) ≤ 4 * (A * S₁) := by nlinarith
    have h2 : A * S₁ ≤ (158 * κ₀) * (κ₀ / 2 ^ T) := mul_le_mul hAκ hS₁κ hS₁.le (by positivity)
    have e : 4 * ((158 * κ₀) * (κ₀ / 2 ^ T)) = (632 * κ₀ ^ 2) / 2 ^ T := by ring
    linarith
  refine ⟨hne, hdet, hent', ?_⟩
  refine hbud.trans ?_
  have i1 : (A * S₁)⁻¹ ≤ (A * S₂)⁻¹ := by
    apply inv_anti₀ (by positivity); nlinarith
  have h2 : A * S₁ + A * S₂ ≤ 2 * ((632 * κ₀ ^ 2) / 2 ^ T) := by
    have h3 : A * S₁ ≤ (158 * κ₀) * (κ₀ / 2 ^ T) := mul_le_mul hAκ hS₁κ hS₁.le (by positivity)
    have h4 : A * S₂ ≤ A * S₁ := by nlinarith
    have e : (158 * κ₀) * (κ₀ / 2 ^ T) = (158 * κ₀ ^ 2) / 2 ^ T := by ring
    have e2 : 2 * ((632 * κ₀ ^ 2) / 2 ^ T) = (1264 * κ₀ ^ 2) / 2 ^ T := by ring
    rw [e2]
    have : (158 * κ₀ ^ 2) / 2 ^ T ≤ (632 * κ₀ ^ 2) / 2 ^ T := by
      gcongr; norm_num
    linarith
  have e3 : 4 / (A * S₂) = 4 * (A * S₂)⁻¹ := by ring
  rw [e3]
  linarith

end Props

end Submission.Obl.k4_compatible_pair_frame_preparation.Construction
