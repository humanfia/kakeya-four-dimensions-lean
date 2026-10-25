-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP.HalfEndgameCore.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.HalfEndgameLemmas
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SP.DenseFamily

/-!
# The parallel-projection endgame at `s = 1/2`

A `HalfConfig` gives, in the cotangent coordinates `a = cot e₁`, `b = cot e₂` of the bush
normals joining a pin to the two base pins, a family of dense sets `G t ⊆ A × B` (one for
each pin of `H`, `t = (h - h₁) / (h₂ - h)`) whose projections `a + t b` are covered by
`4 #D(p)` balls. `dense_family_expansion` forbids this when the losses are small
(`half_endgame_core`; the numeric side conditions are hypotheses).
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP

/-- The body of `dense_family_expansion` for fixed parameters. -/
def FamilyExpansionAt (ε κ δ₀ : ℝ) : Prop :=
  ∀ δ σ C : ℝ, 0 < δ → δ ≤ δ₀ → 1 / 2 ≤ σ → σ ≤ 1 - ε →
    1 ≤ C → C ≤ δ ^ (-κ) →
    ∀ A B S : Finset ℝ, A.Nonempty → B.Nonempty → S.Nonempty →
      (∀ s ∈ S, s ∈ Set.Icc (0 : ℝ) 1) →
      RealFiniteFrostman δ C σ A → RealFiniteFrostman δ C σ B →
      RealFiniteFrostman δ C σ S →
      (∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a') →
      (∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → δ ≤ dist b b') →
      (A.card : ℝ) ≤ δ ^ (-σ - κ) → (B.card : ℝ) ≤ δ ^ (-σ - κ) →
      ∀ G : ℝ → Finset (ℝ × ℝ), (∀ t ∈ S, G t ⊆ A ×ˢ B) →
        (∀ t ∈ S, δ ^ κ * (A.card : ℝ) * (B.card : ℝ) ≤ ((G t).card : ℝ)) →
        ∃ t ∈ S, CoverLower δ
          ((fun p : ℝ × ℝ => p.1 + t * p.2) '' (↑(G t) : Set (ℝ × ℝ)))
          (δ ^ (-κ) * (A.card : ℝ))

theorem exists_familyExpansionAt (ε : ℝ) (hε : 0 < ε) :
    ∃ κ δ₀ : ℝ, 0 < κ ∧ 0 < δ₀ ∧ δ₀ ≤ 1 ∧ FamilyExpansionAt ε κ δ₀ :=
  dense_family_expansion ε hε

/-- Grid snapping. -/
noncomputable def snap (δ x : ℝ) : ℝ := δ * (realGridIndex δ x : ℝ)

theorem snap_error {δ : ℝ} (hδ : 0 < δ) (x : ℝ) : |snap δ x - x| ≤ δ := by
  have h := realGridIndex_error hδ x
  unfold snap
  rw [abs_le]
  constructor <;> linarith

theorem snap_sep {δ : ℝ} (hδ : 0 < δ) {x y : ℝ} (h : snap δ x ≠ snap δ y) :
    δ ≤ dist (snap δ x) (snap δ y) := by
  unfold snap at *
  have hk : realGridIndex δ x ≠ realGridIndex δ y := fun e => h (by rw [e])
  rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hδ]
  have h1 : (1 : ℤ) ≤ |realGridIndex δ x - realGridIndex δ y| :=
    Int.one_le_abs (sub_ne_zero.mpr hk)
  have h2 : (1 : ℝ) ≤ |((realGridIndex δ x : ℝ) - (realGridIndex δ y : ℝ))| := by
    have := (Int.cast_le (R := ℝ)).mpr h1
    push_cast at this
    exact this
  nlinarith

theorem bush_card_le {r K : ℝ} {E : Finset Plane} (hE : HalfBush r K E) (hr : 0 < r)
    (hr2 : r ≤ 2) : (E.card : ℝ) ≤ K * (2 / r) ^ (1 / 2 : ℝ) := by
  obtain ⟨hunit, _, hKT⟩ := hE
  let u : Plane := EuclideanSpace.single 0 1
  have hu : ‖u‖ = 1 := by simp [u]
  have h := hKT u hu 2 hr2
  have hfil : E.filter (fun e => dist e u ≤ 2) = E := by
    apply Finset.filter_true_of_mem
    intro e he
    calc dist e u ≤ ‖e‖ + ‖u‖ := by rw [dist_eq_norm]; exact norm_sub_le _ _
      _ = 2 := by rw [hunit e he, hu]; norm_num
  rw [hfil] at h
  exact h

theorem between_bounds {h h₁ h₂ : ℝ} (hbet : 0 ≤ (h - h₁) * (h₂ - h))
    (hcl : |h - h₁| ≤ |h₂ - h|) :
    |h₂ - h| ≤ |h₂ - h₁| ∧ |h₂ - h₁| ≤ 2 * |h₂ - h| ∧ 0 ≤ (h₂ - h₁) * (h₂ - h) := by
  have e : h₂ - h₁ = (h₂ - h) + (h - h₁) := by ring
  refine ⟨?_, ?_, ?_⟩
  · apply sq_le_sq.mp
    rw [e]
    nlinarith [sq_nonneg (h - h₁)]
  · rw [e]
    calc |h₂ - h + (h - h₁)| ≤ |h₂ - h| + |h - h₁| := abs_add_le _ _
      _ ≤ 2 * |h₂ - h| := by linarith
  · rw [e]
    nlinarith [sq_nonneg (h₂ - h)]

/-- The time parameter of a pin on `ℓ₀` and its inverse Lipschitz bound. -/
theorem tparam_sub {h h' h₁ h₂ : ℝ} (hgap : 0 < |h₂ - h₁|)
    (hbet : 0 ≤ (h - h₁) * (h₂ - h)) (hcl : |h - h₁| ≤ |h₂ - h|)
    (hbet' : 0 ≤ (h' - h₁) * (h₂ - h')) (hcl' : |h' - h₁| ≤ |h₂ - h'|)
    (h16 : |h₂ - h₁| ≤ 16) :
    |h - h'| ≤ 16 * |(h - h₁) / (h₂ - h) - (h' - h₁) / (h₂ - h')| := by
  obtain ⟨b1, b2, _⟩ := between_bounds hbet hcl
  obtain ⟨b1', b2', _⟩ := between_bounds hbet' hcl'
  have hd : 0 < |h₂ - h| := by linarith
  have hd' : 0 < |h₂ - h'| := by linarith
  have hne : h₂ - h ≠ 0 := abs_pos.mp hd
  have hne' : h₂ - h' ≠ 0 := abs_pos.mp hd'
  have e : (h - h₁) / (h₂ - h) - (h' - h₁) / (h₂ - h') =
      (h - h') * (h₂ - h₁) / ((h₂ - h) * (h₂ - h')) := by
    field_simp
    ring
  rw [e, abs_div, abs_mul, abs_mul]
  have hle : |h₂ - h| * |h₂ - h'| ≤ |h₂ - h₁| * 16 := by
    have h3 : |h₂ - h| * |h₂ - h'| ≤ |h₂ - h₁| * |h₂ - h₁| :=
      mul_le_mul b1 b1' hd'.le hgap.le
    nlinarith
  rw [mul_div_assoc', le_div_iff₀ (mul_pos hd hd')]
  have := abs_nonneg (h - h')
  nlinarith

theorem tparam_mem {h h₁ h₂ : ℝ} (hgap : 0 < |h₂ - h₁|) (hbet : 0 ≤ (h - h₁) * (h₂ - h))
    (hcl : |h - h₁| ≤ |h₂ - h|) : (h - h₁) / (h₂ - h) ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨_, b2, _⟩ := between_bounds hbet hcl
  have hd : 0 < |h₂ - h| := by linarith
  have hne : h₂ - h ≠ 0 := abs_pos.mp hd
  constructor
  · have e : (h - h₁) / (h₂ - h) = (h - h₁) * (h₂ - h) / (h₂ - h) ^ 2 := by
      field_simp
    rw [e]
    positivity
  · have h1 : |(h - h₁) / (h₂ - h)| ≤ 1 := by
      rw [abs_div, div_le_one hd]
      exact hcl
    exact (le_abs_self _).trans h1

set_option maxHeartbeats 4000000 in
/-- **The parallel-projection endgame**, with explicit numeric side conditions. -/
theorem half_endgame_core {κ' δ₀' : ℝ} (hfam : FamilyExpansionAt (1 / 4) κ' δ₀')
    {r K c δ M Kb Lg La CA : ℝ} {n p₀ p₁ p₂ : Plane} {H Q : Finset Plane}
    {D Qh : Plane → Finset Plane}
    (hcfg : HalfConfig r K c n p₀ p₁ p₂ H Q D Qh)
    (hr : 0 < r) (hc : 0 < c) (hc1 : c ≤ 1) (hrc : 64 * r ≤ c / 8) (hK : 1 ≤ K)
    (hδ : δ = 16384 * r / c ^ 2) (hM : M = 225 * (6600 * δ / (c ^ 2 * r)) ^ 2)
    (hKb : Kb = K * (2 / r) ^ (1 / 2 : ℝ)) (hLg : Lg = (K * K * r * M)⁻¹)
    (hLa : La = Lg / Kb) (hCA : CA = 2 * K * (4 / (c / 64 * r)) ^ (1 / 2 : ℝ) / La)
    (hδ₀ : δ ≤ δ₀') (hC : CA ≤ δ ^ (-κ')) (hCS : 6 * K ≤ δ ^ (-κ'))
    (hKbd : Kb ≤ δ ^ (-(1 / 2) - κ')) (hdens : δ ^ κ' * Kb ^ 2 ≤ Lg)
    (hcov : 4 * Kb < δ ^ (-κ') * La) : False := by
  classical
  have hn := hcfg.unit_normal
  have hc16 : c ≤ 16 := by linarith
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hc2 : c ^ 2 ≤ 1 := by nlinarith
  have hrδ : r ≤ δ := by
    rw [hδ, le_div_iff₀ (by positivity)]
    nlinarith
  have hr2 : r ≤ 2 := by linarith
  have hc' : 0 < c / 64 := by positivity
  have hK0 : 0 < K := by linarith
  have hKb0 : 0 < Kb := by rw [hKb]; positivity
  have hM0 : 0 < M := by rw [hM]; positivity
  have hLg0 : 0 < Lg := by rw [hLg]; positivity
  have hLa0 : 0 < La := by rw [hLa]; positivity
  -- positions
  have hb₁ : ‖p₁ - p₀‖ ≤ 8 := hcfg.line_bounded p₁ (Finset.mem_insert_self _ _)
  have hb₂ : ‖p₂ - p₀‖ ≤ 8 :=
    hcfg.line_bounded p₂ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hbH : ∀ p ∈ H, ‖p - p₀‖ ≤ 8 := fun p hp =>
    hcfg.line_bounded p (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp))
  have hdist : ∀ q ∈ Q, ∀ p : Plane, ‖p - p₀‖ ≤ 8 → ‖q - p‖ ≤ 16 := by
    intro q hq p hp
    calc ‖q - p‖ = ‖(q - p₀) - (p - p₀)‖ := by congr 1; abel
      _ ≤ ‖q - p₀‖ + ‖p - p₀‖ := norm_sub_le _ _
      _ ≤ 16 := by linarith [hcfg.pins_bounded q hq]
  set h₁ := alongCoord n p₀ p₁ with hh₁def
  set h₂ := alongCoord n p₀ p₂ with hh₂def
  have hh₁ : |h₁| ≤ 8 := abs_alongCoord_le hn hb₁
  have hh₂ : |h₂| ≤ 8 := abs_alongCoord_le hn hb₂
  have hgap : c ≤ |h₂ - h₁| := hcfg.base_gap
  have hgap' : 0 < |h₂ - h₁| := hc.trans_le hgap
  have h16 : |h₂ - h₁| ≤ 16 := by
    rw [abs_le]
    constructor <;> linarith [abs_le.mp hh₁, abs_le.mp hh₂]
  have hfarQ : ∀ q ∈ Q, c ≤ |acrossCoord n p₀ q| := fun q hq =>
    (hcfg.pins_far q hq).trans (le_abs_self _)
  -- bushes
  have hbush₁ : HalfBush r K (D p₁) := hcfg.bush p₁ (Finset.mem_insert_self _ _)
  have hbush₂ : HalfBush r K (D p₂) :=
    hcfg.bush p₂ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hbushH : ∀ p ∈ H, HalfBush r K (D p) := fun p hp =>
    hcfg.bush p (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ hp)))
  -- joined normals
  choose! e₁ he₁D he₁r using hcfg.join₁
  choose! e₂ he₂D he₂r using hcfg.join₂
  have hjh : ∀ p ∈ H, ∀ q ∈ Qh p, ∃ e ∈ D p, |inner ℝ (q - p) e| ≤ 64 * r :=
    fun p hp => (hcfg.line_dense p hp).2.2
  choose! eh hehD hehr using hjh
  have hQh : ∀ p ∈ H, Qh p ⊆ Q := fun p hp => (hcfg.line_dense p hp).1
  -- normals are not parallel to `ℓ₀`
  have hw₁ : ∀ q ∈ Q, c / 64 ≤ |inner ℝ (e₁ q) (perp n)| := fun q hq =>
    normal_along_lower hn (hbush₁.1 _ (he₁D q hq)) hc hc16 hrc (he₁r q hq)
      hcfg.base_on_line.1 (hfarQ q hq) (hdist q hq p₁ hb₁)
  have hw₂ : ∀ q ∈ Q, c / 64 ≤ |inner ℝ (e₂ q) (perp n)| := fun q hq =>
    normal_along_lower hn (hbush₂.1 _ (he₂D q hq)) hc hc16 hrc (he₂r q hq)
      hcfg.base_on_line.2 (hfarQ q hq) (hdist q hq p₂ hb₂)
  have hwh : ∀ p ∈ H, ∀ q ∈ Qh p, c / 64 ≤ |inner ℝ (eh p q) (perp n)| := fun p hp q hq =>
    normal_along_lower hn ((hbushH p hp).1 _ (hehD p hp q hq)) hc hc16 hrc (hehr p hp q hq)
      (hcfg.line_pins p hp).1 (hfarQ q (hQh p hp hq)) (hdist q (hQh p hp hq) p (hbH p hp))
  -- cotangent errors
  have herr : 2 * (64 * r) / (c * (c / 64)) = δ / 2 := by
    rw [hδ]
    field_simp
    ring
  have hcot₁ : ∀ q ∈ Q, |cotNormal n (e₁ q) -
      (alongCoord n p₀ q - h₁) / acrossCoord n p₀ q| ≤ δ / 2 := by
    intro q hq
    have h := joined_cot hn (hbush₁.1 _ (he₁D q hq)) hc hc' (he₁r q hq) hcfg.base_on_line.1
      (hfarQ q hq) (hw₁ q hq)
    rwa [herr] at h
  have hcot₂ : ∀ q ∈ Q, |cotNormal n (e₂ q) -
      (alongCoord n p₀ q - h₂) / acrossCoord n p₀ q| ≤ δ / 2 := by
    intro q hq
    have h := joined_cot hn (hbush₂.1 _ (he₂D q hq)) hc hc' (he₂r q hq) hcfg.base_on_line.2
      (hfarQ q hq) (hw₂ q hq)
    rwa [herr] at h
  have hcoth : ∀ p ∈ H, ∀ q ∈ Qh p, |cotNormal n (eh p q) -
      (alongCoord n p₀ q - alongCoord n p₀ p) / acrossCoord n p₀ q| ≤ δ / 2 := by
    intro p hp q hq
    have h := joined_cot hn ((hbushH p hp).1 _ (hehD p hp q hq)) hc hc' (hehr p hp q hq)
      (hcfg.line_pins p hp).1 (hfarQ q (hQh p hp hq)) (hwh p hp q hq)
    rwa [herr] at h
  -- the cotangent sets
  set E₁ := (D p₁).filter (fun e => c / 64 ≤ |inner ℝ e (perp n)|) with hE₁
  set E₂ := (D p₂).filter (fun e => c / 64 ≤ |inner ℝ e (perp n)|) with hE₂
  set A := (E₁.image (cotNormal n)).image (snap δ) with hA
  set B := (E₂.image (cotNormal n)).image (snap δ) with hB
  have hAsep : ∀ a ∈ A, ∀ a' ∈ A, a ≠ a' → δ ≤ dist a a' := by
    intro a ha a' ha' hne
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp ha'
    exact snap_sep hδpos hne
  have hBsep : ∀ b ∈ B, ∀ b' ∈ B, b ≠ b' → δ ≤ dist b b' := by
    intro a ha a' ha' hne
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp ha'
    exact snap_sep hδpos hne
  have hAcard : (A.card : ℝ) ≤ Kb := by
    have h1 : A.card ≤ (D p₁).card :=
      Finset.card_image_le.trans (Finset.card_image_le.trans (Finset.card_filter_le _ _))
    have h2 := bush_card_le hbush₁ hr hr2
    rw [hKb]
    exact (by exact_mod_cast h1 : (A.card : ℝ) ≤ (D p₁).card).trans h2
  have hBcard : (B.card : ℝ) ≤ Kb := by
    have h1 : B.card ≤ (D p₂).card :=
      Finset.card_image_le.trans (Finset.card_image_le.trans (Finset.card_filter_le _ _))
    have h2 := bush_card_le hbush₂ hr hr2
    rw [hKb]
    exact (by exact_mod_cast h1 : (B.card : ℝ) ≤ (D p₂).card).trans h2
  -- the scalars
  let tf : Plane → ℝ := fun p => (alongCoord n p₀ p - h₁) / (h₂ - alongCoord n p₀ p)
  set S := H.image tf with hS
  have hpin : ∀ t ∈ S, ∃ p ∈ H, tf p = t := by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨p, hp, rfl⟩
  choose! pin hpinH hpint using hpin
  -- the dense sets
  let φ : Plane → ℝ × ℝ := fun q => (snap δ (cotNormal n (e₁ q)), snap δ (cotNormal n (e₂ q)))
  let G : ℝ → Finset (ℝ × ℝ) := fun t => (Qh (pin t)).image φ
  have hφA : ∀ q ∈ Q, (φ q).1 ∈ A := by
    intro q hq
    exact Finset.mem_image.mpr ⟨cotNormal n (e₁ q), Finset.mem_image.mpr ⟨e₁ q,
      Finset.mem_filter.mpr ⟨he₁D q hq, hw₁ q hq⟩, rfl⟩, rfl⟩
  have hφB : ∀ q ∈ Q, (φ q).2 ∈ B := by
    intro q hq
    exact Finset.mem_image.mpr ⟨cotNormal n (e₂ q), Finset.mem_image.mpr ⟨e₂ q,
      Finset.mem_filter.mpr ⟨he₂D q hq, hw₂ q hq⟩, rfl⟩, rfl⟩
  have hGsub : ∀ t ∈ S, G t ⊆ A ×ˢ B := by
    intro t ht v hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
    have hqQ := hQh (pin t) (hpinH t ht) hq
    exact Finset.mem_product.mpr ⟨hφA q hqQ, hφB q hqQ⟩
  -- fibers of `φ`
  have hfiber : ∀ q ∈ Q, ∀ q' ∈ Q, φ q = φ q' → dist q q' ≤ 6600 * δ / c ^ 2 := by
    intro q hq q' hq' heq
    have ha : snap δ (cotNormal n (e₁ q)) = snap δ (cotNormal n (e₁ q')) :=
      congrArg Prod.fst heq
    have hb : snap δ (cotNormal n (e₂ q)) = snap δ (cotNormal n (e₂ q')) :=
      congrArg Prod.snd heq
    have hα : |(alongCoord n p₀ q - h₁) / acrossCoord n p₀ q -
        (alongCoord n p₀ q' - h₁) / acrossCoord n p₀ q'| ≤ 3 * δ := by
      have e1 := abs_le.mp (snap_error hδpos (cotNormal n (e₁ q)))
      have e2 := abs_le.mp (snap_error hδpos (cotNormal n (e₁ q')))
      have c1 := abs_le.mp (hcot₁ q hq)
      have c2 := abs_le.mp (hcot₁ q' hq')
      rw [ha] at e1
      rw [abs_le]
      constructor <;> linarith
    have hβ : |(alongCoord n p₀ q - h₂) / acrossCoord n p₀ q -
        (alongCoord n p₀ q' - h₂) / acrossCoord n p₀ q'| ≤ 3 * δ := by
      have e1 := abs_le.mp (snap_error hδpos (cotNormal n (e₂ q)))
      have e2 := abs_le.mp (snap_error hδpos (cotNormal n (e₂ q')))
      have c1 := abs_le.mp (hcot₂ q hq)
      have c2 := abs_le.mp (hcot₂ q' hq')
      rw [hb] at e1
      rw [abs_le]
      constructor <;> linarith
    have h := pin_dist_le_of_cots hn hc hc1 hgap hh₁ (hcfg.pins_far q hq) (hcfg.pins_far q' hq')
      (hcfg.pins_bounded q hq) (hcfg.pins_bounded q' hq')
    calc dist q q' ≤ 1100 / c ^ 2 * (3 * δ + 3 * δ) := h.trans (by
          apply mul_le_mul_of_nonneg_left (by linarith) (by positivity))
      _ = 6600 * δ / c ^ 2 := by ring
  have hRr : r ≤ 6600 * δ / c ^ 2 := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  -- the dense sets are large
  have hGcard : ∀ t ∈ S, Lg ≤ ((G t).card : ℝ) := by
    intro t ht
    have hp := hpinH t ht
    obtain ⟨hQhQ, hQhcard, _⟩ := hcfg.line_dense (pin t) hp
    have hfib : ∀ v ∈ (Qh (pin t)).image φ,
        (((Qh (pin t)).filter (fun q => φ q = v)).card : ℝ) ≤ M := by
      intro v hv
      obtain ⟨q₀, hq₀, rfl⟩ := Finset.mem_image.mp hv
      have h := separated_card_le_ball hr hRr ((Qh (pin t)).filter (fun q => φ q = φ q₀)) q₀
        (fun x hx => hfiber x (hQhQ (Finset.mem_filter.mp hx).1) q₀ (hQhQ hq₀)
          (Finset.mem_filter.mp hx).2)
        (fun x hx y hy hne => hcfg.pins_sep x (hQhQ (Finset.mem_filter.mp hx).1) y
          (hQhQ (Finset.mem_filter.mp hy).1) hne)
      rw [hM]
      have e : 6600 * δ / c ^ 2 / r = 6600 * δ / (c ^ 2 * r) := by
        field_simp
      rwa [e] at h
    have hsum : ((Qh (pin t)).card : ℝ) ≤ M * ((G t).card : ℝ) := by
      have h := Finset.card_eq_sum_card_image φ (Qh (pin t))
      have h' : ((Qh (pin t)).card : ℝ) = ∑ v ∈ (Qh (pin t)).image φ,
          (((Qh (pin t)).filter (fun q => φ q = v)).card : ℝ) := by
        exact_mod_cast h
      rw [h']
      calc ∑ v ∈ (Qh (pin t)).image φ, (((Qh (pin t)).filter (fun q => φ q = v)).card : ℝ)
          ≤ ∑ v ∈ (Qh (pin t)).image φ, M := Finset.sum_le_sum hfib
        _ = M * ((G t).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    have hQlow : K⁻¹ * (K⁻¹ * r⁻¹) ≤ ((Qh (pin t)).card : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_left hcfg.pins_many (by positivity)) hQhcard
    rw [hLg]
    have e : (K * K * r * M)⁻¹ = K⁻¹ * (K⁻¹ * r⁻¹) / M := by
      field_simp
    rw [e, div_le_iff₀ hM0]
    linarith
  -- the scalars are in the unit interval, nonempty, Frostman
  have hSunit : ∀ s ∈ S, s ∈ Set.Icc (0 : ℝ) 1 := by
    intro s hs
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨_, hl, hh⟩ := hcfg.line_pins p hp
    exact tparam_mem hgap' hl hh
  have hSne : S.Nonempty := hcfg.line_nonempty.image _
  have hScard : S.card = H.card := by
    apply Finset.card_image_of_injOn
    intro p hp p' hp' heq
    by_contra hne
    have hsep := hcfg.line_sep p hp p' hp' hne
    obtain ⟨_, hl, hh⟩ := hcfg.line_pins p hp
    obtain ⟨_, hl', hh'⟩ := hcfg.line_pins p' hp'
    have h := tparam_sub hgap' hl hh hl' hh' h16
    have heq' : tf p = tf p' := heq
    simp only [tf] at heq'
    rw [heq', sub_self, abs_zero, mul_zero] at h
    linarith
  have hSF : RealFiniteFrostman δ (6 * K) (1 / 2) S := by
    intro x ρ hρ
    have hρr : r ≤ ρ := hrδ.trans hρ
    rcases (S.filter (fun s => dist s x ≤ ρ)).eq_empty_or_nonempty with h0 | ⟨s₀, hs₀⟩
    · rw [h0, Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith) _))
        (Nat.cast_nonneg _)
    · obtain ⟨hs₀S, hs₀x⟩ := Finset.mem_filter.mp hs₀
      obtain ⟨p₀', hp₀', rfl⟩ := Finset.mem_image.mp hs₀S
      have hsub : S.filter (fun s => dist s x ≤ ρ) ⊆
          (H.filter (fun p => |alongCoord n p₀ p - alongCoord n p₀ p₀'| ≤ 32 * ρ)).image tf := by
        intro s hs
        obtain ⟨hsS, hsx⟩ := Finset.mem_filter.mp hs
        obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hsS
        refine Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, ?_⟩, rfl⟩
        obtain ⟨_, hl, hh⟩ := hcfg.line_pins p hp
        obtain ⟨_, hl', hh'⟩ := hcfg.line_pins p₀' hp₀'
        have h := tparam_sub hgap' hl hh hl' hh' h16
        have hd : |tf p - tf p₀'| ≤ 2 * ρ := by
          rw [Real.dist_eq] at hsx hs₀x
          calc |tf p - tf p₀'| ≤ |tf p - x| + |x - tf p₀'| := abs_sub_le _ _ _
            _ ≤ 2 * ρ := by rw [abs_sub_comm x]; linarith
        calc |alongCoord n p₀ p - alongCoord n p₀ p₀'| ≤ 16 * |tf p - tf p₀'| := h
          _ ≤ 32 * ρ := by linarith
      have hcount := hcfg.line_frostman (alongCoord n p₀ p₀') (32 * ρ) (by linarith)
      have h1 : ((S.filter (fun s => dist s x ≤ ρ)).card : ℝ) ≤
          ((H.filter (fun p => |alongCoord n p₀ p - alongCoord n p₀ p₀'| ≤ 32 * ρ)).card : ℝ) := by
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
      have h32 : (32 * ρ) ^ (1 / 2 : ℝ) ≤ 6 * ρ ^ (1 / 2 : ℝ) := by
        rw [Real.mul_rpow (by norm_num) (by linarith)]
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
        rw [show (32 : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt 32 by rw [Real.sqrt_eq_rpow]]
        rw [Real.sqrt_le_left (by norm_num)]
        norm_num
      rw [hScard]
      calc ((S.filter (fun s => dist s x ≤ ρ)).card : ℝ) ≤ K * (32 * ρ) ^ (1 / 2 : ℝ) * (H.card : ℝ) :=
            h1.trans hcount
        _ ≤ K * (6 * ρ ^ (1 / 2 : ℝ)) * (H.card : ℝ) := by
            apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h32 hK0.le)
              (Nat.cast_nonneg _)
        _ = 6 * K * ρ ^ (1 / 2 : ℝ) * (H.card : ℝ) := by ring
  -- lower bounds for `#A` and `#B`
  obtain ⟨t₀, ht₀⟩ := hSne
  have hGAB : ((G t₀).card : ℝ) ≤ (A.card : ℝ) * (B.card : ℝ) := by
    have := Finset.card_le_card (hGsub t₀ ht₀)
    rw [Finset.card_product] at this
    exact_mod_cast this
  have hAlow : La ≤ (A.card : ℝ) := by
    rw [hLa, div_le_iff₀ hKb0]
    have h1 := hGcard t₀ ht₀
    have h2 : (A.card : ℝ) * (B.card : ℝ) ≤ (A.card : ℝ) * Kb :=
      mul_le_mul_of_nonneg_left hBcard (Nat.cast_nonneg _)
    linarith
  have hBlow : La ≤ (B.card : ℝ) := by
    rw [hLa, div_le_iff₀ hKb0]
    have h1 := hGcard t₀ ht₀
    have h2 : (A.card : ℝ) * (B.card : ℝ) ≤ Kb * (B.card : ℝ) :=
      mul_le_mul_of_nonneg_right hAcard (Nat.cast_nonneg _)
    linarith
  have hAne : A.Nonempty := Finset.card_pos.mp (by exact_mod_cast hLa0.trans_le hAlow)
  have hBne : B.Nonempty := Finset.card_pos.mp (by exact_mod_cast hLa0.trans_le hBlow)
  -- Frostman of the cotangent sets
  have hcotF : ∀ (E : Finset Plane) (Z : Finset ℝ), HalfBush r K E →
      Z = ((E.filter (fun e => c / 64 ≤ |inner ℝ e (perp n)|)).image (cotNormal n)).image
        (snap δ) → La ≤ (Z.card : ℝ) → RealFiniteFrostman δ CA (1 / 2) Z := by
    intro E Z hE hZ hZlow x ρ hρ
    have hsub : Z.filter (fun a => dist a x ≤ ρ) ⊆
        (E.filter (fun e => c / 64 ≤ |inner ℝ e (perp n)| ∧ |cotNormal n e - x| ≤ ρ + δ)).image
          (fun e => snap δ (cotNormal n e)) := by
      intro a ha
      obtain ⟨haZ, hax⟩ := Finset.mem_filter.mp ha
      rw [hZ] at haZ
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp haZ
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨heE, hew⟩ := Finset.mem_filter.mp he
      refine Finset.mem_image.mpr ⟨e, Finset.mem_filter.mpr ⟨heE, hew, ?_⟩, rfl⟩
      have hs := abs_le.mp (snap_error hδpos (cotNormal n e))
      rw [Real.dist_eq] at hax
      have hax' := abs_le.mp hax
      rw [abs_le]
      constructor <;> linarith
    have hcount := cot_value_count (x := x) (R := ρ + δ) hn hr hc' hK0.le hE (by nlinarith)
    have h0 : ((Z.filter (fun a => dist a x ≤ ρ)).card : ℝ) ≤
        ((E.filter (fun e => c / 64 ≤ |inner ℝ e (perp n)| ∧
          |cotNormal n e - x| ≤ ρ + δ)).card : ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
    have h1 : ((Z.filter (fun a => dist a x ≤ ρ)).card : ℝ) ≤
        2 * K * (2 * (ρ + δ) / (c / 64 * r)) ^ (1 / 2 : ℝ) := h0.trans hcount
    have hc'r : 0 < c / 64 * r := by positivity
    have h2 : (2 * (ρ + δ) / (c / 64 * r)) ^ (1 / 2 : ℝ) ≤
        (4 / (c / 64 * r)) ^ (1 / 2 : ℝ) * ρ ^ (1 / 2 : ℝ) := by
      have hρ0 : 0 ≤ ρ := by linarith
      have e : 4 / (c / 64 * r) * ρ = 4 * ρ / (c / 64 * r) := by ring
      rw [← Real.mul_rpow (div_nonneg (by norm_num) hc'r.le) hρ0, e]
      apply Real.rpow_le_rpow (div_nonneg (by linarith) hc'r.le) _ (by norm_num)
      exact div_le_div_of_nonneg_right (by linarith) hc'r.le
    have hCAeq : CA * La = 2 * K * (4 / (c / 64 * r)) ^ (1 / 2 : ℝ) := by
      rw [hCA]
      field_simp
    have hρp : 0 ≤ ρ ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
    calc ((Z.filter (fun a => dist a x ≤ ρ)).card : ℝ)
        ≤ 2 * K * ((4 / (c / 64 * r)) ^ (1 / 2 : ℝ) * ρ ^ (1 / 2 : ℝ)) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
      _ = CA * La * ρ ^ (1 / 2 : ℝ) := by rw [hCAeq]; ring
      _ ≤ CA * (Z.card : ℝ) * ρ ^ (1 / 2 : ℝ) := by
          have hCA0 : 0 ≤ CA := by rw [hCA]; positivity
          apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hZlow hCA0) hρp
      _ = CA * ρ ^ (1 / 2 : ℝ) * (Z.card : ℝ) := by ring
  have hAF : RealFiniteFrostman δ CA (1 / 2) A := hcotF (D p₁) A hbush₁ rfl hAlow
  have hBF : RealFiniteFrostman δ CA (1 / 2) B := hcotF (D p₂) B hbush₂ rfl hBlow
  -- apply the family expansion
  set C := max CA (6 * K) with hCdef
  have hC1 : 1 ≤ C := le_trans (by linarith) (le_max_right _ _)
  have hCle : C ≤ δ ^ (-κ') := max_le hC hCS
  have hAF' : RealFiniteFrostman δ C (1 / 2) A :=
    RealFiniteFrostman.weaken (C := CA) hAF hδpos (le_max_left _ _)
  have hBF' : RealFiniteFrostman δ C (1 / 2) B :=
    RealFiniteFrostman.weaken (C := CA) hBF hδpos (le_max_left _ _)
  have hSF' : RealFiniteFrostman δ C (1 / 2) S :=
    RealFiniteFrostman.weaken (C := 6 * K) hSF hδpos (le_max_right _ _)
  have hAc' : (A.card : ℝ) ≤ δ ^ (-(1 / 2) - κ') := hAcard.trans hKbd
  have hBc' : (B.card : ℝ) ≤ δ ^ (-(1 / 2) - κ') := hBcard.trans hKbd
  have hGdense : ∀ t ∈ S, δ ^ κ' * (A.card : ℝ) * (B.card : ℝ) ≤ ((G t).card : ℝ) := by
    intro t ht
    have h1 : (A.card : ℝ) * (B.card : ℝ) ≤ Kb ^ 2 := by
      rw [pow_two]
      exact mul_le_mul hAcard hBcard (Nat.cast_nonneg _) hKb0.le
    have h2 : δ ^ κ' * ((A.card : ℝ) * (B.card : ℝ)) ≤ δ ^ κ' * Kb ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hδpos.le _)
    rw [mul_assoc]
    linarith [hGcard t ht]
  obtain ⟨t, htS, hlower⟩ := hfam δ (1 / 2) C hδpos hδ₀ le_rfl (by norm_num) hC1 hCle A B S
    hAne hBne ⟨t₀, ht₀⟩ hSunit hAF' hBF' hSF' hAsep hBsep hAc' hBc' G hGsub hGdense
  -- an explicit small cover of the projection
  set p := pin t with hpdef
  have hp := hpinH t htS
  have htp : tf p = t := hpint t htS
  set h := alongCoord n p₀ p with hhdef
  obtain ⟨hYp, hbet, hcl⟩ := hcfg.line_pins p hp
  obtain ⟨b1, b2, b3⟩ := between_bounds hbet hcl
  have hdabs : 0 < |h₂ - h| := by linarith
  have hd : h₂ - h ≠ 0 := abs_pos.mp hdabs
  set lam := (h₂ - h₁) / (h₂ - h) with hlam
  have hlam2 : lam ≤ 2 := by
    rw [hlam]
    calc (h₂ - h₁) / (h₂ - h) ≤ |(h₂ - h₁) / (h₂ - h)| := le_abs_self _
      _ = |h₂ - h₁| / |h₂ - h| := abs_div _ _
      _ ≤ 2 := by rw [div_le_iff₀ hdabs]; linarith
  have hlam0 : 0 ≤ lam := by
    rw [hlam]
    have e : (h₂ - h₁) / (h₂ - h) = (h₂ - h₁) * (h₂ - h) / (h₂ - h) ^ 2 := by
      field_simp
    rw [e]
    exact div_nonneg b3 (sq_nonneg _)
  have ht01 := hSunit t htS
  set Ep := (D p).filter (fun e => c / 64 ≤ |inner ℝ e (perp n)|) with hEp
  set Cset := (Ep.image (fun e => lam * cotNormal n e)).biUnion
    (fun v => ({v - 3 * δ, v - δ, v + δ, v + 3 * δ} : Finset ℝ)) with hCset
  have hCcard : (Cset.card : ℝ) ≤ 4 * Kb := by
    have h1 : Cset.card ≤ (Ep.image (fun e => lam * cotNormal n e)).card * 4 := by
      apply Finset.card_biUnion_le_card_mul
      intro v _
      exact Finset.card_le_four
    have h2 : (Ep.image (fun e => lam * cotNormal n e)).card ≤ (D p).card :=
      Finset.card_image_le.trans (Finset.card_filter_le _ _)
    have h3 := bush_card_le (hbushH p hp) hr hr2
    have h4 : (Cset.card : ℝ) ≤ ((D p).card : ℝ) * 4 := by
      exact_mod_cast h1.trans (Nat.mul_le_mul_right 4 h2)
    rw [hKb]
    linarith
  have hcover : ∀ x ∈ (fun v : ℝ × ℝ => v.1 + t * v.2) '' (↑(G t) : Set (ℝ × ℝ)),
      ∃ y ∈ Cset, dist x y ≤ δ := by
    rintro x ⟨v, hv, rfl⟩
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hv)
    have hqQ : q ∈ Q := hQh p hp hq
    set e := eh p q
    have heEp : e ∈ Ep := Finset.mem_filter.mpr ⟨hehD p hp q hq, hwh p hp q hq⟩
    -- the key estimate
    have hY : acrossCoord n p₀ q ≠ 0 := by
      have := hcfg.pins_far q hqQ
      intro h0
      rw [h0] at this
      linarith
    have hident : (alongCoord n p₀ q - h₁) / acrossCoord n p₀ q +
        t * ((alongCoord n p₀ q - h₂) / acrossCoord n p₀ q) =
          lam * ((alongCoord n p₀ q - h) / acrossCoord n p₀ q) := by
      rw [← htp, hlam]
      simp only [tf]
      have hd' : h₂ - alongCoord n p₀ p ≠ 0 := hd
      have hg : h₂ - h₁ ≠ 0 := abs_pos.mp hgap'
      field_simp
      ring
    have hkey : |(φ q).1 + t * (φ q).2 - lam * cotNormal n e| ≤ 4 * δ := by
      have e1 := abs_le.mp (snap_error hδpos (cotNormal n (e₁ q)))
      have e2 := abs_le.mp (snap_error hδpos (cotNormal n (e₂ q)))
      have c1 := abs_le.mp (hcot₁ q hqQ)
      have c2 := abs_le.mp (hcot₂ q hqQ)
      have c3 := abs_le.mp (hcoth p hp q hq)
      have hdecomp : (φ q).1 + t * (φ q).2 - lam * cotNormal n e =
          ((φ q).1 - (alongCoord n p₀ q - h₁) / acrossCoord n p₀ q) +
            t * ((φ q).2 - (alongCoord n p₀ q - h₂) / acrossCoord n p₀ q) +
              lam * ((alongCoord n p₀ q - h) / acrossCoord n p₀ q - cotNormal n e) := by
        rw [mul_sub, mul_sub, ← hident]
        ring
      rw [hdecomp]
      have ht0 := ht01.1
      have ht1 := ht01.2
      set u := (φ q).1 - (alongCoord n p₀ q - h₁) / acrossCoord n p₀ q
      set w := (φ q).2 - (alongCoord n p₀ q - h₂) / acrossCoord n p₀ q
      set z := (alongCoord n p₀ q - h) / acrossCoord n p₀ q - cotNormal n e
      have hu : |u| ≤ 3 * δ / 2 := by
        simp only [u, φ]
        rw [abs_le]
        constructor <;> linarith
      have hw : |w| ≤ 3 * δ / 2 := by
        simp only [w, φ]
        rw [abs_le]
        constructor <;> linarith
      have hz : |z| ≤ δ / 2 := by
        simp only [z]
        rw [abs_le]
        constructor <;> linarith
      calc |u + t * w + lam * z| ≤ |u| + |t * w| + |lam * z| := abs_add_three _ _ _
        _ = |u| + t * |w| + lam * |z| := by
            rw [abs_mul, abs_mul, abs_of_nonneg ht0, abs_of_nonneg hlam0]
        _ ≤ 3 * δ / 2 + 1 * (3 * δ / 2) + 2 * (δ / 2) := by
            gcongr
        _ = 4 * δ := by ring
    set v0 := lam * cotNormal n e
    have hv0 : v0 ∈ Ep.image (fun e => lam * cotNormal n e) := Finset.mem_image_of_mem _ heEp
    set x := (φ q).1 + t * (φ q).2
    have hx := abs_le.mp hkey
    by_cases h1 : x - v0 ≤ -2 * δ
    · refine ⟨v0 - 3 * δ, Finset.mem_biUnion.mpr ⟨v0, hv0, by simp⟩, ?_⟩
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith
    by_cases h2 : x - v0 ≤ 0
    · refine ⟨v0 - δ, Finset.mem_biUnion.mpr ⟨v0, hv0, by simp⟩, ?_⟩
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith
    by_cases h3 : x - v0 ≤ 2 * δ
    · refine ⟨v0 + δ, Finset.mem_biUnion.mpr ⟨v0, hv0, by simp⟩, ?_⟩
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith
    · refine ⟨v0 + 3 * δ, Finset.mem_biUnion.mpr ⟨v0, hv0, by simp⟩, ?_⟩
      rw [Real.dist_eq, abs_le]
      constructor <;> linarith
  obtain ⟨m, cc, hcc, hm⟩ := cover_of_centers Cset _ hcover
  have hlow := hlower m cc hcc
  have hA' : δ ^ (-κ') * La ≤ δ ^ (-κ') * (A.card : ℝ) :=
    mul_le_mul_of_nonneg_left hAlow (Real.rpow_nonneg hδpos.le _)
  linarith

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half.SP
