-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High.Hairbrush.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Reused from workspace o157/x0672 WangZahlLot/Obl/wz_furstenberg_bush_line_count/High/Hairbrush.lean (c552951).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.Classes
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.High.AtScale

/-!
# The hairbrush lower bound for the number of lines (Wolff's leaf)

Labels `D` over points `P`, every label sent by `cls` to a line of `J₀` (a label `j` read
as the line through `j.1` with unit normal `j.2`), with the geometry of
`FailData.classes`: `|⟨q.1 - (cls q).1, (cls q).2⟩| < 9 δ` and `q.2` within `δ` of
`± (cls q).2`.

`hairbrush_lower`: take the richest line `j*`. Through each of its pins, keep the normals at
angle more than `θ₀` from `± j*.2`. Their lines are transverse to `j*`, and a transverse
line meets the pins of `j*` in at most `Npk` points (hypothesis `hpack`, a packing bound for
the intersection of two transverse strips). Hence
`#P · Nb · (Nb - 2 Kθ) ≤ 4 Kδ ^ 2 Npk #J₀ ^ 2`, where every bush has at least `Nb` normals,
at most `Kθ` normals in any `θ₀`-ball and at most `Kδ` normals in any `δ`-ball.

With `Npk ≈ 1 / θ₀` (`pins_near_transverse_close`: two pins near both of two transverse
lines are within `150 δ / θ₀`), this is Wolff's bound `#J₀ ≳ #P ^ (1/2) Nb`, which beats
`Nb ^ 2` once the points are more than twice as dimensional as the bushes.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half

attribute [local instance] Classical.propDecidable

noncomputable section

/-- Two pins near two transverse lines are close: if `p, p'` are within `9 δ` of the lines
`(a, e)` and `(b, f)` (unit normals), and `f` is `θ₀ / 2`-far from `± e`, then
`dist p p' < 150 δ / θ₀`. -/
theorem pins_near_transverse_close {δ θ₀ : ℝ} (hδ : 0 < δ) (hθ₀ : 0 < θ₀) (hθ₀2 : θ₀ ≤ 2)
    {a b e f p p' : E2} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hfar : θ₀ / 2 ≤ dist f e ∧ θ₀ / 2 ≤ dist f (-e))
    (hpe : |inner ℝ (p - a) e| < 9 * δ) (hp'e : |inner ℝ (p' - a) e| < 9 * δ)
    (hpf : |inner ℝ (p - b) f| < 9 * δ) (hp'f : |inner ℝ (p' - b) f| < 9 * δ) :
    dist p p' < 150 * δ / θ₀ := by
  by_contra hlong
  push Not at hlong
  set lam := 150 * δ / θ₀ with hlam
  have hlam0 : 0 < lam := by positivity
  set v := p - p' with hv
  have hvlong : lam ≤ ‖v‖ := by rw [hv, ← dist_eq_norm]; exact hlong
  have hve : |inner ℝ v e| < 18 * δ := by
    have : inner ℝ v e = inner ℝ (p - a) e - inner ℝ (p' - a) e := by
      rw [← inner_sub_left]; congr 1; rw [hv]; abel
    rw [this]
    calc |inner ℝ (p - a) e - inner ℝ (p' - a) e|
        ≤ |inner ℝ (p - a) e| + |inner ℝ (p' - a) e| := abs_sub _ _
      _ < 9 * δ + 9 * δ := add_lt_add hpe hp'e
      _ = 18 * δ := by ring
  have hvf : |inner ℝ v f| < 18 * δ := by
    have : inner ℝ v f = inner ℝ (p - b) f - inner ℝ (p' - b) f := by
      rw [← inner_sub_left]; congr 1; rw [hv]; abel
    rw [this]
    calc |inner ℝ (p - b) f - inner ℝ (p' - b) f|
        ≤ |inner ℝ (p - b) f| + |inner ℝ (p' - b) f| := abs_sub _ _
      _ < 9 * δ + 9 * δ := add_lt_add hpf hp'f
      _ = 18 * δ := by ring
  have hratio : 18 * δ / lam = 18 * θ₀ / 150 := by
    rw [hlam]; field_simp
  have hsmall : (18 * δ / lam) ^ 2 ≤ 1 / 2 := by
    rw [hratio]
    have : 18 * θ₀ / 150 ≤ 36 / 150 := by linarith
    have h0 : 0 ≤ 18 * θ₀ / 150 := by positivity
    nlinarith
  have hclose := normals_close_of_long_vector hlam0 he hf hvlong hve hvf hsmall hsmall
  have hbound : 3 * ((18 * δ + 18 * δ) / lam) ^ 2 = 3 * (36 * θ₀ / 150) ^ 2 := by
    rw [hlam]; field_simp; ring
  have hfar2 : (θ₀ / 2) ^ 2 ≤ ‖e - f‖ ^ 2 ∧ (θ₀ / 2) ^ 2 ≤ ‖e - -f‖ ^ 2 := by
    constructor
    · have h1 : θ₀ / 2 ≤ ‖e - f‖ := by rw [← dist_eq_norm, dist_comm]; exact hfar.1
      exact pow_le_pow_left₀ (by positivity) h1 2
    · have h1 : θ₀ / 2 ≤ ‖e - -f‖ := by
        rw [← dist_eq_norm]
        have : dist e (-f) = dist f (-e) := by
          rw [dist_comm, ← dist_neg_neg, neg_neg]
        rw [this]; exact hfar.2
      exact pow_le_pow_left₀ (by positivity) h1 2
  have hlt : 3 * (36 * θ₀ / 150) ^ 2 < (θ₀ / 2) ^ 2 := by
    have : 0 < θ₀ ^ 2 := by positivity
    nlinarith
  rcases hclose with h | h <;> rw [hbound] at h
  · linarith [hfar2.1]
  · linarith [hfar2.2]

/-- Labels at one point whose normal is within `δ` of `± u` number at most `2 Kδ`. -/
theorem labels_near_pm_le {δ Kδ : ℝ} {D : Finset (E2 × E2)} {p u : E2} (hu : ‖u‖ = 1)
    (hkδ : ∀ w : E2, ‖w‖ = 1 → (((bushOf D p).filter (fun e => dist e w ≤ δ)).card : ℝ) ≤ Kδ)
    (A : Finset (E2 × E2)) (hA : ∀ q ∈ A, q ∈ D ∧ q.1 = p ∧ (dist q.2 u < δ ∨ dist q.2 (-u) < δ)) :
    (A.card : ℝ) ≤ 2 * Kδ := by
  classical
  have hun : ‖-u‖ = 1 := by rw [norm_neg, hu]
  have hinj : Set.InjOn Prod.snd (A : Set (E2 × E2)) := by
    intro q hq q' hq' heq
    exact Prod.ext (((hA q hq).2.1).trans ((hA q' hq').2.1).symm) heq
  have hsub : A.image Prod.snd ⊆ (bushOf D p).filter (fun e => dist e u ≤ δ) ∪
      (bushOf D p).filter (fun e => dist e (-u) ≤ δ) := by
    intro e he
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hqD, hqp, hnear⟩ := hA q hq
    have hb : q.2 ∈ bushOf D p := by rw [mem_bushOf, ← hqp]; exact hqD
    rcases hnear with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hb, h.le⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hb, h.le⟩)
  calc (A.card : ℝ) = ((A.image Prod.snd).card : ℝ) := by
        rw [Finset.card_image_of_injOn hinj]
    _ ≤ (((bushOf D p).filter (fun e => dist e u ≤ δ) ∪
          (bushOf D p).filter (fun e => dist e (-u) ≤ δ)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ (((bushOf D p).filter (fun e => dist e u ≤ δ)).card : ℝ) +
          (((bushOf D p).filter (fun e => dist e (-u) ≤ δ)).card : ℝ) := by
        exact_mod_cast Finset.card_union_le _ _
    _ ≤ Kδ + Kδ := add_le_add (hkδ u hu) (hkδ (-u) hun)
    _ = 2 * Kδ := by ring

/-- **The hairbrush bound.** `#P · Nb · (Nb - 2 Kθ) ≤ 4 Kδ ^ 2 Npk #J₀ ^ 2`. -/
theorem hairbrush_lower {δ θ₀ Nb Kθ Kδ Npk : ℝ} (hθ₀δ : 2 * δ ≤ θ₀) (hNb : 2 * Kθ ≤ Nb)
    (hKδ : 0 ≤ Kδ) (hNpk : 0 ≤ Npk)
    {P : Finset E2} {D J₀ : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hD : ∀ q ∈ D, q.1 ∈ P ∧ ‖q.2‖ = 1) (hPne : P.Nonempty) (hNb0 : 0 < Nb)
    (hbush : ∀ p ∈ P, Nb ≤ ((bushOf D p).card : ℝ))
    (hkθ : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 →
      (((bushOf D p).filter (fun e => dist e u ≤ θ₀)).card : ℝ) ≤ Kθ)
    (hkδ : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 →
      (((bushOf D p).filter (fun e => dist e u ≤ δ)).card : ℝ) ≤ Kδ)
    (hcls : ∀ q ∈ D, cls q ∈ J₀)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * δ ∧
      (dist q.2 (cls q).2 < δ ∨ dist q.2 (-(cls q).2) < δ))
    (hJunit : ∀ j ∈ J₀, ‖j.2‖ = 1)
    (hpack : ∀ j ∈ J₀, ∀ j' ∈ J₀, θ₀ / 2 ≤ dist j'.2 j.2 → θ₀ / 2 ≤ dist j'.2 (-j.2) →
      ((P.filter (fun p => |inner ℝ (p - j.1) j.2| < 9 * δ ∧
        |inner ℝ (p - j'.1) j'.2| < 9 * δ)).card : ℝ) ≤ Npk) :
    (P.card : ℝ) * Nb * (Nb - 2 * Kθ) ≤ 4 * Kδ ^ 2 * Npk * (J₀.card : ℝ) ^ 2 := by
  classical
  -- labels and classes
  have hDcard : (P.card : ℝ) * Nb ≤ (D.card : ℝ) := by
    rw [card_eq_sum_bushOf (fun q hq => (hD q hq).1)]
    calc (P.card : ℝ) * Nb = ∑ _p ∈ P, Nb := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun p hp => hbush p hp)
  obtain ⟨p₀, hp₀⟩ := hPne
  have hDne : D.Nonempty := by
    have h1 := hbush p₀ hp₀
    have hpos : (0 : ℝ) < (bushOf D p₀).card := lt_of_lt_of_le hNb0 h1
    obtain ⟨e, he⟩ := Finset.card_pos.mp (by exact_mod_cast hpos)
    exact ⟨(p₀, e), mem_bushOf.mp he⟩
  have hJne : J₀.Nonempty := by
    obtain ⟨q, hq⟩ := hDne
    exact ⟨cls q, hcls q hq⟩
  have hJpos : (0 : ℝ) < J₀.card := by exact_mod_cast hJne.card_pos
  set n : E2 × E2 → ℝ := fun j => ((D.filter (fun q => cls q = j)).card : ℝ) with hndef
  have hsumn : ∑ j ∈ J₀, n j = (D.card : ℝ) := by
    have := Finset.card_eq_sum_card_fiberwise (f := cls) (s := D) (t := J₀) hcls
    simp only [hndef]
    exact_mod_cast this.symm
  obtain ⟨jst, hjst, hjrich⟩ : ∃ j ∈ J₀, (D.card : ℝ) / J₀.card ≤ n j := by
    apply Finset.exists_le_of_sum_le hJne
    rw [hsumn, Finset.sum_const, nsmul_eq_mul]
    field_simp
    exact le_refl _
  set est := jst.2 with hest
  have hest1 : ‖est‖ = 1 := hJunit jst hjst
  -- the pins of the richest class
  set H := (D.filter (fun q => cls q = jst)).image Prod.fst with hH
  have hHP : ∀ p ∈ H, p ∈ P := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    exact (hD q (Finset.mem_filter.mp hq).1).1
  have hHnear : ∀ p ∈ H, |inner ℝ (p - jst.1) est| < 9 * δ := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hqD, hqc⟩ := Finset.mem_filter.mp hq
    have h := (hgeo q hqD).1
    rw [hqc] at h
    exact h
  have hnH : n jst ≤ (H.card : ℝ) * (2 * Kδ) := by
    have h1 : n jst = ∑ p ∈ H,
        (((D.filter (fun q => cls q = jst)).filter (fun q => q.1 = p)).card : ℝ) := by
      have := Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
        (s := D.filter (fun q => cls q = jst)) (t := H)
        (fun q hq => Finset.mem_image.mpr ⟨q, hq, rfl⟩)
      simp only [hndef]
      exact_mod_cast this
    rw [h1]
    calc ∑ p ∈ H, (((D.filter (fun q => cls q = jst)).filter (fun q => q.1 = p)).card : ℝ)
        ≤ ∑ _p ∈ H, 2 * Kδ := by
          apply Finset.sum_le_sum
          intro p hp
          apply labels_near_pm_le hest1 (hkδ p (hHP p hp))
          intro q hq
          obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
          obtain ⟨hqD, hqc⟩ := Finset.mem_filter.mp hq1
          have hg := (hgeo q hqD).2
          rw [hqc] at hg
          exact ⟨hqD, hq2, hg⟩
      _ = (H.card : ℝ) * (2 * Kδ) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- the transverse labels at the pins of the richest class
  set Λ := D.filter (fun q => q.1 ∈ H ∧ θ₀ < dist q.2 est ∧ θ₀ < dist q.2 (-est)) with hΛ
  have hΛlow : (H.card : ℝ) * (Nb - 2 * Kθ) ≤ (Λ.card : ℝ) := by
    have h1 : (Λ.card : ℝ) = ∑ p ∈ H, ((Λ.filter (fun q => q.1 = p)).card : ℝ) := by
      have := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := Λ) (t := H)
        (fun q hq => (Finset.mem_filter.mp hq).2.1)
      exact_mod_cast this
    rw [h1]
    calc (H.card : ℝ) * (Nb - 2 * Kθ) = ∑ _p ∈ H, (Nb - 2 * Kθ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ p ∈ H, ((Λ.filter (fun q => q.1 = p)).card : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          have hpP := hHP p hp
          have hestn : ‖-est‖ = 1 := by rw [norm_neg, hest1]
          -- the bush splits into the two θ₀-caps and the transverse normals
          have hsplit : bushOf D p ⊆ (bushOf D p).filter (fun e => dist e est ≤ θ₀) ∪
              (bushOf D p).filter (fun e => dist e (-est) ≤ θ₀) ∪
              (Λ.filter (fun q => q.1 = p)).image Prod.snd := by
            intro e he
            by_cases h1 : dist e est ≤ θ₀
            · exact Finset.mem_union_left _ (Finset.mem_union_left _
                (Finset.mem_filter.mpr ⟨he, h1⟩))
            by_cases h2 : dist e (-est) ≤ θ₀
            · exact Finset.mem_union_left _ (Finset.mem_union_right _
                (Finset.mem_filter.mpr ⟨he, h2⟩))
            push Not at h1 h2
            apply Finset.mem_union_right
            refine Finset.mem_image.mpr ⟨(p, e), ?_, rfl⟩
            refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨mem_bushOf.mp he, hp, h1, h2⟩, rfl⟩
          have hc := Finset.card_le_card hsplit
          have hc2 := Finset.card_union_le
            ((bushOf D p).filter (fun e => dist e est ≤ θ₀) ∪
              (bushOf D p).filter (fun e => dist e (-est) ≤ θ₀))
            ((Λ.filter (fun q => q.1 = p)).image Prod.snd)
          have hc3 := Finset.card_union_le
            ((bushOf D p).filter (fun e => dist e est ≤ θ₀))
            ((bushOf D p).filter (fun e => dist e (-est) ≤ θ₀))
          have hc4 := Finset.card_image_le (s := Λ.filter (fun q => q.1 = p)) (f := Prod.snd)
          have hk1 := hkθ p hpP est hest1
          have hk2 := hkθ p hpP (-est) hestn
          have hb := hbush p hpP
          have : (((bushOf D p)).card : ℝ) ≤ Kθ + Kθ + ((Λ.filter (fun q => q.1 = p)).card : ℝ) := by
            have h := (hc.trans hc2).trans (Nat.add_le_add_right hc3 _)
            have h' : ((bushOf D p).card : ℝ) ≤
                (((bushOf D p).filter (fun e => dist e est ≤ θ₀)).card : ℝ) +
                (((bushOf D p).filter (fun e => dist e (-est) ≤ θ₀)).card : ℝ) +
                (((Λ.filter (fun q => q.1 = p)).image Prod.snd).card : ℝ) := by
              exact_mod_cast h
            have h4 : (((Λ.filter (fun q => q.1 = p)).image Prod.snd).card : ℝ) ≤
                ((Λ.filter (fun q => q.1 = p)).card : ℝ) := by exact_mod_cast hc4
            linarith
          linarith
  -- each class receives few transverse labels
  have hfib : ∀ j ∈ J₀, ((Λ.filter (fun q => cls q = j)).card : ℝ) ≤ 2 * Kδ * Npk := by
    intro j hj
    by_cases hje : (Λ.filter (fun q => cls q = j)).Nonempty
    · obtain ⟨q₁, hq₁⟩ := hje
      obtain ⟨hq₁Λ, hq₁c⟩ := Finset.mem_filter.mp hq₁
      obtain ⟨hq₁D, -, hfar1, hfar2⟩ := Finset.mem_filter.mp hq₁Λ
      have hj1 : ‖j.2‖ = 1 := hJunit j hj
      -- the class `j` is transverse to `jst`
      have hg1 := (hgeo q₁ hq₁D).2
      rw [hq₁c] at hg1
      have htr : θ₀ / 2 ≤ dist j.2 est ∧ θ₀ / 2 ≤ dist j.2 (-est) := by
        rcases hg1 with h | h
        · constructor
          · have := dist_triangle q₁.2 j.2 est
            linarith
          · have := dist_triangle q₁.2 j.2 (-est)
            linarith
        · constructor
          · have h3 := dist_triangle q₁.2 (-j.2) (-est)
            have hn : dist (-j.2) (-est) = dist j.2 est := dist_neg_neg _ _
            rw [hn] at h3
            linarith
          · have h3 := dist_triangle q₁.2 (-j.2) est
            have hn : dist (-j.2) est = dist j.2 (-est) := by
              rw [← dist_neg_neg, neg_neg]
            rw [hn] at h3
            linarith
      have hP := hpack jst hjst j hj htr.1 htr.2
      -- labels of class `j` grouped by their pins
      set Pj := (Λ.filter (fun q => cls q = j)).image Prod.fst with hPj
      have hPjsub : Pj ⊆ P.filter (fun p => |inner ℝ (p - jst.1) jst.2| < 9 * δ ∧
          |inner ℝ (p - j.1) j.2| < 9 * δ) := by
        intro p hp
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
        obtain ⟨hqΛ, hqc⟩ := Finset.mem_filter.mp hq
        obtain ⟨hqD, hqH, -, -⟩ := Finset.mem_filter.mp hqΛ
        have hg := (hgeo q hqD).1
        rw [hqc] at hg
        exact Finset.mem_filter.mpr ⟨(hD q hqD).1, hHnear q.1 hqH, hg⟩
      have hPjcard : (Pj.card : ℝ) ≤ Npk :=
        (Nat.cast_le.mpr (Finset.card_le_card hPjsub)).trans hP
      have h1 : ((Λ.filter (fun q => cls q = j)).card : ℝ) = ∑ p ∈ Pj,
          (((Λ.filter (fun q => cls q = j)).filter (fun q => q.1 = p)).card : ℝ) := by
        have := Finset.card_eq_sum_card_fiberwise (f := Prod.fst)
          (s := Λ.filter (fun q => cls q = j)) (t := Pj)
          (fun q hq => Finset.mem_image.mpr ⟨q, hq, rfl⟩)
        exact_mod_cast this
      rw [h1]
      calc ∑ p ∈ Pj, (((Λ.filter (fun q => cls q = j)).filter (fun q => q.1 = p)).card : ℝ)
          ≤ ∑ _p ∈ Pj, 2 * Kδ := by
            apply Finset.sum_le_sum
            intro p hp
            have hpP : p ∈ P := (Finset.mem_filter.mp (hPjsub hp)).1
            apply labels_near_pm_le hj1 (hkδ p hpP)
            intro q hq
            obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
            obtain ⟨hqΛ, hqc⟩ := Finset.mem_filter.mp hq1
            have hqD := (Finset.mem_filter.mp hqΛ).1
            have hg := (hgeo q hqD).2
            rw [hqc] at hg
            exact ⟨hqD, hq2, hg⟩
        _ = (Pj.card : ℝ) * (2 * Kδ) := by rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ Npk * (2 * Kδ) := mul_le_mul_of_nonneg_right hPjcard (by linarith)
        _ = 2 * Kδ * Npk := by ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hje, Finset.card_empty, Nat.cast_zero]
      positivity
  -- combine
  have hΛup : (Λ.card : ℝ) ≤ (J₀.card : ℝ) * (2 * Kδ * Npk) := by
    have hmaps : ∀ q ∈ Λ, cls q ∈ J₀ := fun q hq => hcls q (Finset.mem_filter.mp hq).1
    have h1 := Finset.card_eq_sum_card_fiberwise hmaps
    have h2 : (Λ.card : ℝ) = ∑ j ∈ J₀, ((Λ.filter (fun q => cls q = j)).card : ℝ) := by
      exact_mod_cast h1
    rw [h2]
    calc ∑ j ∈ J₀, ((Λ.filter (fun q => cls q = j)).card : ℝ) ≤ ∑ _j ∈ J₀, 2 * Kδ * Npk :=
          Finset.sum_le_sum hfib
      _ = (J₀.card : ℝ) * (2 * Kδ * Npk) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hrich : (P.card : ℝ) * Nb ≤ (J₀.card : ℝ) * n jst := by
    have h := (div_le_iff₀ hJpos).mp hjrich
    linarith
  have hd0 : 0 ≤ Nb - 2 * Kθ := by linarith
  calc (P.card : ℝ) * Nb * (Nb - 2 * Kθ) ≤ (J₀.card : ℝ) * n jst * (Nb - 2 * Kθ) :=
        mul_le_mul_of_nonneg_right hrich hd0
    _ ≤ (J₀.card : ℝ) * ((H.card : ℝ) * (2 * Kδ)) * (Nb - 2 * Kθ) := by
        apply mul_le_mul_of_nonneg_right _ hd0
        exact mul_le_mul_of_nonneg_left hnH hJpos.le
    _ = (J₀.card : ℝ) * (2 * Kδ) * ((H.card : ℝ) * (Nb - 2 * Kθ)) := by ring
    _ ≤ (J₀.card : ℝ) * (2 * Kδ) * (Λ.card : ℝ) := by
        apply mul_le_mul_of_nonneg_left hΛlow
        positivity
    _ ≤ (J₀.card : ℝ) * (2 * Kδ) * ((J₀.card : ℝ) * (2 * Kδ * Npk)) := by
        apply mul_le_mul_of_nonneg_left hΛup
        positivity
    _ = 4 * Kδ ^ 2 * Npk * (J₀.card : ℝ) ^ 2 := by ring

/-- The packing hypothesis of `hairbrush_lower` from a ball count: the pins near two
`θ₀ / 2`-transverse lines lie in one ball of radius `150 δ / θ₀`. -/
theorem transverse_pack_of_ball {δ θ₀ Npk : ℝ} (hδ : 0 < δ) (hθ₀ : 0 < θ₀) (hθ₀2 : θ₀ ≤ 2)
    (hNpk : 0 ≤ Npk) {P : Finset E2}
    (hball : ∀ x ∈ P, ((P.filter (fun p => dist p x ≤ 150 * δ / θ₀)).card : ℝ) ≤ Npk)
    {j j' : E2 × E2} (hj : ‖j.2‖ = 1) (hj' : ‖j'.2‖ = 1)
    (htr1 : θ₀ / 2 ≤ dist j'.2 j.2) (htr2 : θ₀ / 2 ≤ dist j'.2 (-j.2)) :
    ((P.filter (fun p => |inner ℝ (p - j.1) j.2| < 9 * δ ∧
        |inner ℝ (p - j'.1) j'.2| < 9 * δ)).card : ℝ) ≤ Npk := by
  classical
  set W := P.filter (fun p => |inner ℝ (p - j.1) j.2| < 9 * δ ∧
    |inner ℝ (p - j'.1) j'.2| < 9 * δ) with hW
  by_cases hWe : W = ∅
  · rw [hWe, Finset.card_empty, Nat.cast_zero]; exact hNpk
  obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hWe
  obtain ⟨hxP, hx1, hx2⟩ := Finset.mem_filter.mp hx
  refine le_trans ?_ (hball x hxP)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hpP, hp1, hp2⟩ := Finset.mem_filter.mp hp
  refine Finset.mem_filter.mpr ⟨hpP, ?_⟩
  exact (pins_near_transverse_close hδ hθ₀ hθ₀2 hj hj' ⟨htr1, htr2⟩ hp1 hx1 hp2 hx2).le

/-- A `δ`-separated set has at most `(6 R / δ + 3) ^ 2` points in a closed ball of radius
`R`: the grid squares of side `δ / 3` separate its points. -/
theorem separated_ball_card_le {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R) {P : Finset E2}
    (hsep : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → δ ≤ dist p p') (x : E2) :
    ((P.filter (fun p => dist p x ≤ R)).card : ℝ) ≤ (6 * R / δ + 3) ^ 2 := by
  classical
  set W := P.filter (fun p => dist p x ≤ R) with hW
  set h := δ / 3 with hh
  have hh0 : 0 < h := by positivity
  -- the grid index of `p - x` at mesh `h`
  let idx : E2 → ℤ × ℤ := fun p => cellOf h (p - x)
  have hinj : Set.InjOn idx (W : Set E2) := by
    intro p hp p' hp' heq
    by_contra hne
    have hd := dist_le_of_cellOf_eq hh0 heq
    have hd' : dist (p - x) (p' - x) = dist p p' := by
      rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
    rw [hd'] at hd
    have := hsep p (Finset.mem_filter.mp hp).1 p' (Finset.mem_filter.mp hp').1 hne
    rw [hh] at hd
    linarith
  -- every index lies in a box of side `6 R / δ + 3`
  set N : ℤ := ⌈3 * R / δ⌉ with hN
  have hNr : (N : ℝ) = ((⌈3 * R / δ⌉ : ℤ) : ℝ) := by rw [hN]
  have hceil := Int.le_ceil (3 * R / δ)
  have hceil' := Int.ceil_lt_add_one (3 * R / δ)
  have hbox : ∀ p ∈ W, idx p ∈ Finset.Icc (-N) N ×ˢ Finset.Icc (-N) N := by
    intro p hp
    have hpR : dist p x ≤ R := (Finset.mem_filter.mp hp).2
    have hcoord : ∀ i : Fin 2, |(p - x) i| ≤ R := by
      intro i
      calc |(p - x) i| ≤ ‖p - x‖ := by
            have := EuclideanSpace.norm_eq (p - x)
            rw [this]
            calc |(p - x) i| = Real.sqrt (((p - x) i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
              _ ≤ Real.sqrt (∑ j, ‖(p - x) j‖ ^ 2) := by
                  apply Real.sqrt_le_sqrt
                  have hterm : ((p - x) i) ^ 2 = ‖(p - x) i‖ ^ 2 := by
                    rw [Real.norm_eq_abs, sq_abs]
                  rw [hterm]
                  exact Finset.single_le_sum (f := fun j => ‖(p - x) j‖ ^ 2)
                    (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        _ = dist p x := (dist_eq_norm p x).symm
        _ ≤ R := hpR
    have hfl : ∀ i : Fin 2, -N ≤ ⌊(p - x) i / h⌋ ∧ ⌊(p - x) i / h⌋ ≤ N := by
      intro i
      have hc := abs_le.mp (hcoord i)
      have hdiv1 : (p - x) i / h ≤ 3 * R / δ := by
        rw [hh, div_div_eq_mul_div, div_le_div_iff_of_pos_right hδ]; linarith
      have hdiv2 : -(3 * R / δ) ≤ (p - x) i / h := by
        rw [hh, div_div_eq_mul_div, ← neg_div, div_le_div_iff_of_pos_right hδ]
        linarith [hc.1]
      constructor
      · have h1 : (-N : ℤ) ≤ ⌊(p - x) i / h⌋ := by
          rw [Int.le_floor]
          push_cast
          rw [hNr]
          linarith
        exact h1
      · have h2 : ⌊(p - x) i / h⌋ ≤ N := by
          have h3 : ⌊(p - x) i / h⌋ ≤ ⌈3 * R / δ⌉ := by
            exact (Int.floor_le_floor hdiv1).trans (Int.floor_le_ceil _)
          linarith
        exact h2
    simp only [idx, cellOf, Finset.mem_product, Finset.mem_Icc]
    exact ⟨hfl 0, hfl 1⟩
  have hcard : W.card ≤ (Finset.Icc (-N) N ×ˢ Finset.Icc (-N) N).card :=
    Finset.card_le_card_of_injOn idx (fun p hp => hbox p hp) hinj
  rw [Finset.card_product, Int.card_Icc] at hcard
  have hN0 : 0 ≤ N := by
    have := Int.le_ceil (3 * R / δ)
    have h0 : (0 : ℝ) ≤ 3 * R / δ := by positivity
    have : (0 : ℤ) ≤ ⌈3 * R / δ⌉ := Int.ceil_nonneg h0
    omega
  have hlen : ((N + 1 - -N).toNat : ℝ) ≤ 6 * R / δ + 3 := by
    have h1 : N + 1 - -N = 2 * N + 1 := by ring
    rw [h1]
    have h2 : (0 : ℤ) ≤ 2 * N + 1 := by omega
    rw [show ((2 * N + 1).toNat : ℝ) = ((2 * N + 1 : ℤ) : ℝ) by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg h2]]
    push_cast
    rw [hNr]
    have h4 : 2 * (3 * R / δ) = 6 * R / δ := by ring
    linarith
  calc (W.card : ℝ) ≤ (((N + 1 - -N).toNat * (N + 1 - -N).toNat : ℕ) : ℝ) := by
        exact_mod_cast hcard
    _ = ((N + 1 - -N).toNat : ℝ) * ((N + 1 - -N).toNat : ℝ) := by push_cast; ring
    _ ≤ (6 * R / δ + 3) * (6 * R / δ + 3) :=
        mul_le_mul hlen hlen (Nat.cast_nonneg _) (by positivity)
    _ = (6 * R / δ + 3) ^ 2 := by ring

/-- **Separated hairbrush (Wolff leaf).** For a `δ`-separated pin set whose bushes have at least
`Nb` normals, at most `Kθ` in any `θ₀`-cap and at most `Kδ` in any `δ`-cap, and whose labels are
grouped into `δ`-lines `J₀`, the number of lines satisfies
`|P| Nb (Nb - 2 Kθ) ≤ 4 Kδ² (900/θ₀ + 3)² |J₀|²`. -/
theorem separated_hairbrush {δ θ₀ Nb Kθ Kδ : ℝ} (hδ : 0 < δ) (hθ₀δ : 2 * δ ≤ θ₀)
    (hθ₀2 : θ₀ ≤ 2) (hNb : 2 * Kθ ≤ Nb) (hKδ : 0 ≤ Kδ)
    {P : Finset E2} {D J₀ : Finset (E2 × E2)} {cls : E2 × E2 → E2 × E2}
    (hsep : ∀ p ∈ P, ∀ p' ∈ P, p ≠ p' → δ ≤ dist p p')
    (hD : ∀ q ∈ D, q.1 ∈ P ∧ ‖q.2‖ = 1) (hPne : P.Nonempty) (hNb0 : 0 < Nb)
    (hbush : ∀ p ∈ P, Nb ≤ ((bushOf D p).card : ℝ))
    (hkθ : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 →
      (((bushOf D p).filter (fun e => dist e u ≤ θ₀)).card : ℝ) ≤ Kθ)
    (hkδ : ∀ p ∈ P, ∀ u : E2, ‖u‖ = 1 →
      (((bushOf D p).filter (fun e => dist e u ≤ δ)).card : ℝ) ≤ Kδ)
    (hcls : ∀ q ∈ D, cls q ∈ J₀)
    (hgeo : ∀ q ∈ D, |inner ℝ (q.1 - (cls q).1) (cls q).2| < 9 * δ ∧
      (dist q.2 (cls q).2 < δ ∨ dist q.2 (-(cls q).2) < δ))
    (hJunit : ∀ j ∈ J₀, ‖j.2‖ = 1) :
    (P.card : ℝ) * Nb * (Nb - 2 * Kθ) ≤
      4 * Kδ ^ 2 * (900 / θ₀ + 3) ^ 2 * (J₀.card : ℝ) ^ 2 := by
  have hθ₀ : 0 < θ₀ := by linarith
  have hR : 0 ≤ 150 * δ / θ₀ := by positivity
  have hball : ∀ x ∈ P, ((P.filter (fun p => dist p x ≤ 150 * δ / θ₀)).card : ℝ) ≤
      (900 / θ₀ + 3) ^ 2 := by
    intro x _
    have h := separated_ball_card_le hδ hR hsep x
    have he : 6 * (150 * δ / θ₀) / δ = 900 / θ₀ := by field_simp; ring
    rwa [he] at h
  have hNpk : (0 : ℝ) ≤ (900 / θ₀ + 3) ^ 2 := sq_nonneg _
  exact hairbrush_lower hθ₀δ hNb hKδ hNpk hD hPne hNb0 hbush hkθ hkδ hcls hgeo hJunit
    (fun j hj j' hj' htr1 htr2 => transverse_pack_of_ball hδ hθ₀ hθ₀2 hNpk hball
      (hJunit j hj) (hJunit j' hj') htr1 htr2)

end

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.High
