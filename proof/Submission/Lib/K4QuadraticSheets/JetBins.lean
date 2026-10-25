import Mathlib

/-!
# Jet coordinates and jet bins at an anchor

The jets of a function `ℂ³ → ℂ` at an anchor are recorded by finitely many complex coordinates:
the iterated derivatives applied to tuples of standard basis vectors.  The operator norm of a
multilinear map is at most the sum of these coordinates, and each coordinate is at most the
operator norm.  Binning the real and imaginary parts of all coordinates at a common width gives a
label with a fixed finite number of entries: equal labels mean close jets, and close jets have
neighbouring labels, at most `3 ^ (2 · #coordinates)` of them.
-/

namespace Submission.Lib.K4QuadraticSheets

local notation "E3" => EuclideanSpace ℂ (Fin 3)

/-- The standard basis tuple indexed by `r`. -/
noncomputable def basisTuple {j : ℕ} (r : Fin j → Fin 3) : Fin j → E3 :=
  fun k => EuclideanSpace.single (r k) (1 : ℂ)

/-- The operator norm of a multilinear map on `ℂ³` is at most the sum of its values on basis
tuples. -/
theorem norm_le_sum_basis {j : ℕ} (M : ContinuousMultilinearMap ℂ (fun _ : Fin j => E3) ℂ) :
    ‖M‖ ≤ ∑ r : Fin j → Fin 3, ‖M (basisTuple r)‖ := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro m
  have hexp : m = fun k => ∑ i : Fin 3, (m k i) • EuclideanSpace.single i (1 : ℂ) := by
    funext k
    have := (EuclideanSpace.basisFun (Fin 3) ℂ).sum_repr (m k)
    simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at this
    exact this.symm
  calc ‖M m‖ = ‖∑ r : Fin j → Fin 3,
        M (fun k => (m k (r k)) • EuclideanSpace.single (r k) (1 : ℂ))‖ := by
        conv_lhs => rw [hexp]
        rw [ContinuousMultilinearMap.map_sum]
    _ ≤ ∑ r : Fin j → Fin 3,
          ‖M (fun k => (m k (r k)) • EuclideanSpace.single (r k) (1 : ℂ))‖ := norm_sum_le _ _
    _ = ∑ r : Fin j → Fin 3, (∏ k, ‖m k (r k)‖) * ‖M (basisTuple r)‖ := by
        apply Finset.sum_congr rfl
        intro r _
        rw [ContinuousMultilinearMap.map_smul_univ, norm_smul, norm_prod]
        rfl
    _ ≤ ∑ r : Fin j → Fin 3, (∏ k, ‖m k‖) * ‖M (basisTuple r)‖ := by
        apply Finset.sum_le_sum
        intro r _
        gcongr with k _
        exact PiLp.norm_apply_le (m k) (r k)
    _ = (∑ r : Fin j → Fin 3, ‖M (basisTuple r)‖) * ∏ k, ‖m k‖ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r _
        ring

/-- A basis coordinate is at most the operator norm. -/
theorem norm_basis_le {j : ℕ} (M : ContinuousMultilinearMap ℂ (fun _ : Fin j => E3) ℂ)
    (r : Fin j → Fin 3) : ‖M (basisTuple r)‖ ≤ ‖M‖ := by
  apply ContinuousMultilinearMap.unit_le_opNorm
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro k
  simp [basisTuple]

/-- The index set of jet coordinates through order `q`. -/
abbrev JetIdx (q : ℕ) := Σ j : Fin (q + 1), (Fin (j : ℕ) → Fin 3)

/-- The jet coordinates of a function at a point through order `q`. -/
noncomputable def jetCoord (q : ℕ) (f : E3 → ℂ) (α : E3) : JetIdx q → ℂ :=
  fun ι => iteratedFDeriv ℂ (ι.1 : ℕ) f α (basisTuple ι.2)

/-- The bin of a complex number at width `w`: floors of real and imaginary parts. -/
noncomputable def cbin (w : ℝ) (v : ℂ) : ℤ × ℤ := (⌊v.re / w⌋, ⌊v.im / w⌋)

/-- The jet bin (label) of a function at a point. -/
noncomputable def jetBin (q : ℕ) (w : ℝ) (f : E3 → ℂ) (α : E3) : JetIdx q → ℤ × ℤ :=
  fun ι => cbin w (jetCoord q f α ι)

theorem abs_sub_lt_of_floor_eq {w x y : ℝ} (hw : 0 < w) (h : ⌊x / w⌋ = ⌊y / w⌋) :
    |x - y| < w := by
  have h1 := Int.floor_le (x / w)
  have h2 := Int.lt_floor_add_one (x / w)
  have h3 := Int.floor_le (y / w)
  have h4 := Int.lt_floor_add_one (y / w)
  rw [h] at h1 h2
  have : |x / w - y / w| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  rw [← sub_div, abs_div, abs_of_pos hw, div_lt_one hw] at this
  exact this

theorem floor_sub_le_one_of_abs_le {w x y : ℝ} (hw : 0 < w) (h : |x - y| ≤ w) :
    |(⌊x / w⌋ : ℤ) - ⌊y / w⌋| ≤ 1 := by
  have hxy : |x / w - y / w| ≤ 1 := by
    rw [← sub_div, abs_div, abs_of_pos hw, div_le_one hw]; exact h
  rw [abs_le] at hxy ⊢
  have h1 := Int.floor_le (x / w)
  have h2 := Int.lt_floor_add_one (x / w)
  have h3 := Int.floor_le (y / w)
  have h4 := Int.lt_floor_add_one (y / w)
  constructor
  · have : ((⌊y / w⌋ : ℤ) : ℝ) - ⌊x / w⌋ < 2 := by linarith
    have : (⌊y / w⌋ : ℤ) - ⌊x / w⌋ < 2 := by exact_mod_cast this
    omega
  · have : ((⌊x / w⌋ : ℤ) : ℝ) - ⌊y / w⌋ < 2 := by linarith
    have : (⌊x / w⌋ : ℤ) - ⌊y / w⌋ < 2 := by exact_mod_cast this
    omega

/-- Equal bins mean close complex numbers. -/
theorem norm_sub_lt_of_cbin_eq {w : ℝ} (hw : 0 < w) {u v : ℂ} (h : cbin w u = cbin w v) :
    ‖u - v‖ < 2 * w := by
  simp only [cbin, Prod.mk.injEq] at h
  have h1 := abs_sub_lt_of_floor_eq hw h.1
  have h2 := abs_sub_lt_of_floor_eq hw h.2
  calc ‖u - v‖ ≤ |(u - v).re| + |(u - v).im| := Complex.norm_le_abs_re_add_abs_im _
    _ < w + w := by
        rw [Complex.sub_re, Complex.sub_im]
        linarith
    _ = 2 * w := by ring

/-- Close complex numbers have neighbouring bins. -/
theorem cbin_near {w : ℝ} (hw : 0 < w) {u v : ℂ} (h : ‖u - v‖ ≤ w) :
    |(cbin w u).1 - (cbin w v).1| ≤ 1 ∧ |(cbin w u).2 - (cbin w v).2| ≤ 1 := by
  have hre : |u.re - v.re| ≤ w := by
    rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans h
  have him : |u.im - v.im| ≤ w := by
    rw [← Complex.sub_im]; exact (Complex.abs_im_le_norm _).trans h
  exact ⟨floor_sub_le_one_of_abs_le hw hre, floor_sub_le_one_of_abs_le hw him⟩

/-- The finite set of neighbouring labels of a label. -/
noncomputable def nbhdBins {q : ℕ} (b : JetIdx q → ℤ × ℤ) : Finset (JetIdx q → ℤ × ℤ) :=
  Fintype.piFinset fun ι =>
    (Finset.Icc ((b ι).1 - 1) ((b ι).1 + 1)) ×ˢ (Finset.Icc ((b ι).2 - 1) ((b ι).2 + 1))

theorem card_nbhdBins {q : ℕ} (b : JetIdx q → ℤ × ℤ) :
    (nbhdBins b).card = 9 ^ Fintype.card (JetIdx q) := by
  classical
  rw [nbhdBins, Fintype.card_piFinset]
  have : ∀ ι : JetIdx q, ((Finset.Icc ((b ι).1 - 1) ((b ι).1 + 1)) ×ˢ
      (Finset.Icc ((b ι).2 - 1) ((b ι).2 + 1))).card = 9 := by
    intro ι
    rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
    have h1 : (b ι).1 + 1 + 1 - ((b ι).1 - 1) = 3 := by ring
    have h2 : (b ι).2 + 1 + 1 - ((b ι).2 - 1) = 3 := by ring
    rw [h1, h2]
    rfl
  simp only [this, Finset.prod_const, Finset.card_univ]

/-- Close jets have neighbouring jet bins. -/
theorem jetBin_mem_nbhdBins {q : ℕ} {w : ℝ} (hw : 0 < w) {f g : E3 → ℂ} {α : E3}
    (h : ∀ j : ℕ, j ≤ q →
      ‖iteratedFDeriv ℂ j f α - iteratedFDeriv ℂ j g α‖ ≤ w) :
    jetBin q w f α ∈ nbhdBins (jetBin q w g α) := by
  classical
  rw [nbhdBins, Fintype.mem_piFinset]
  intro ι
  have hle := h ι.1 (Nat.lt_succ_iff.mp ι.1.2)
  have hcoord : ‖jetCoord q f α ι - jetCoord q g α ι‖ ≤ w := by
    have := norm_basis_le (iteratedFDeriv ℂ (ι.1 : ℕ) f α - iteratedFDeriv ℂ (ι.1 : ℕ) g α) ι.2
    simp only [ContinuousMultilinearMap.sub_apply] at this
    exact this.trans hle
  obtain ⟨h1, h2⟩ := cbin_near hw hcoord
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  simp only [jetBin]
  rw [abs_le] at h1 h2
  refine ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, ⟨by linarith [h2.1], by linarith [h2.2]⟩⟩

/-- Equal jet bins mean jets within `2 · 3^j · w` in operator norm. -/
theorem norm_iteratedFDeriv_sub_le_of_jetBin_eq {q : ℕ} {w : ℝ} (hw : 0 < w)
    {f g : E3 → ℂ} {α : E3} (h : jetBin q w f α = jetBin q w g α) (j : ℕ) (hj : j ≤ q) :
    ‖iteratedFDeriv ℂ j f α - iteratedFDeriv ℂ j g α‖ ≤ 3 ^ j * (2 * w) := by
  classical
  apply (norm_le_sum_basis _).trans
  have hcoord : ∀ r : Fin j → Fin 3,
      ‖(iteratedFDeriv ℂ j f α - iteratedFDeriv ℂ j g α) (basisTuple r)‖ ≤ 2 * w := by
    intro r
    have := congrFun h ⟨⟨j, Nat.lt_succ_of_le hj⟩, r⟩
    simp only [jetBin, jetCoord] at this
    simp only [ContinuousMultilinearMap.sub_apply]
    exact (norm_sub_lt_of_cbin_eq hw this).le
  calc ∑ r : Fin j → Fin 3, ‖(iteratedFDeriv ℂ j f α - iteratedFDeriv ℂ j g α) (basisTuple r)‖
      ≤ ∑ _r : Fin j → Fin 3, 2 * w := Finset.sum_le_sum (fun r _ => hcoord r)
    _ = 3 ^ j * (2 * w) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

end Submission.Lib.K4QuadraticSheets
