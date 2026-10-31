module

public import ArtGallery.Orthogonal.Hard.NookCert

/-!
# Coverage certificates in a copy nook

The copy nook in its real grid (`nφ`, `nψ`: polynomials in the parameters `G, u − G, e`, frame
`(x_N, 2H)`, `NookCert.lean`) is covered cell by cell.  A cell is cut by lines through *named
points* (grid points and the foot `f = (x_N, 2H + 1 − 5e/4)` of the extended nook segment) into
leaves; a leaf is

* a *guard leaf* (`k = 0`: the AAM helper `(4, 15)`, `k = 1`: the chain helper `(11, 8)`): an item
  (half-planes through named points, and the grid box spanned by the cell and the guard) that
  contains the guard, contains the leaf (each half-plane is a cut of the leaf or holds at the four
  corners of the cell), has a strict inner point, and misses every complement cell of its box
  (one of its half-planes is `≤ 0` at the four corners of the cell);
* the *pocket* (`k = 2`) or the *triangle `Q`* below the nook segment (`k = 3`), containing the
  leaf (same containment test);
* *empty*: a cut is `< 0` at the four corners.

All signs are polynomial signs on the parameter box (`nookDom`), decided by `MP.nnS`/`MP.posS`.
`ntree_sound`: every point of a certified cell is seen by a helper through a segment of the item
(hence of the region), or lies in the pocket, or in `Q`.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Geometry Set

/-! ### Named points, lines, signs -/

/-- A named point of the nook frame: a grid point or the foot `f` of the extended nook segment. -/
inductive NRef
  | g (i j : ℕ)
  | f
  deriving DecidableEq

/-- The polynomial coordinates of a named point (frame `(x_N, 2H)`). -/
def NRef.mp : NRef → MP × MP
  | .g i j => (nXs.getD i [], nYs.getD j [])
  | .f => (MP.c 0, nYB)

/-- A line through two named points (half-plane: left side). -/
abbrev NLn := NRef × NRef

/-- `det` of three polynomial points. -/
def mpDet (u v z : MP × MP) : MP :=
  MP.sub (MP.mul (MP.sub v.1 u.1) (MP.sub z.2 u.2)) (MP.mul (MP.sub z.1 u.1) (MP.sub v.2 u.2))

/-- `det` of a line and a polynomial point. -/
def lnDet (l : NLn) (z : MP × MP) : MP := mpDet l.1.mp l.2.mp z

/-- Robust signs on the parameter box. -/
def nnN (p : MP) : Bool := MP.nnS nookDom (MP.norm p) 6

def posN (p : MP) : Bool := MP.posS nookDom (MP.norm p) 6

/-- A weighted point. -/
def wpt (ws : List (ℚ × NRef)) : MP × MP :=
  (ws.foldr (fun w acc => MP.add (MP.smul w.1 w.2.mp.1) acc) [],
    ws.foldr (fun w acc => MP.add (MP.smul w.1 w.2.mp.2) acc) [])

/-- The corners of a grid cell. -/
def cellCs (c : ℕ × ℕ) : List NRef :=
  [.g c.1 c.2, .g (c.1 + 1) c.2, .g (c.1 + 1) (c.2 + 1), .g c.1 (c.2 + 1)]

/-- The guards: the AAM helper (`0`) and the chain helper (`1`). -/
def nGuardIdx : ℕ → ℕ × ℕ
  | 0 => (4, 15)
  | _ => (11, 8)

/-- The grid box spanned by a cell and a guard. -/
def nBox (c g : ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (min c.1 g.1, max (c.1 + 1) g.1, min c.2 g.2, max (c.2 + 1) g.2)

/-- The four sides of a grid box (counter-clockwise). -/
def boxLns (b : ℕ × ℕ × ℕ × ℕ) : List NLn :=
  [(.g b.1 b.2.2.1, .g b.2.1 b.2.2.1), (.g b.2.1 b.2.2.1, .g b.2.1 b.2.2.2),
    (.g b.2.1 b.2.2.2, .g b.1 b.2.2.2), (.g b.1 b.2.2.2, .g b.1 b.2.2.1)]

/-- The pocket `f, L_m, R_m, N_top`. -/
def pocketLns : List NLn := [(.f, .g 16 3), (.g 16 3, .g 17 3), (.g 17 3, .g 15 12), (.g 15 12, .f)]

/-- The triangle `Q = f, (0, Y₆), (X₁₃, Y₆)` (its third side on the line `f L_m`). -/
def qLns : List NLn := [(.f, .g 15 6), (.g 15 6, .g 13 6), (.f, .g 16 3)]

/-! ### Certificates -/

/-- A cut tree of a cell. -/
inductive NTree
  | leaf (k : ℕ) (ls : List NLn) (w : List (ℚ × NRef)) (seps : List ((ℕ × ℕ) × ℕ))
  | empty (l : NLn)
  | lin (l : NLn) (t1 t2 : NTree)

def holdsB (l : NLn) (c : ℕ × ℕ) : Bool := (cellCs c).all fun q => nnN (lnDet l q.mp)

def offCellB (l : NLn) (c : ℕ × ℕ) : Bool := (cellCs c).all fun q => nnN (MP.neg (lnDet l q.mp))

def emptyB (l : NLn) (c : ℕ × ℕ) : Bool := (cellCs c).all fun q => posN (MP.neg (lnDet l q.mp))

def containB (ls cuts : List NLn) (c : ℕ × ℕ) : Bool :=
  ls.all fun l => decide (l ∈ cuts) || holdsB l c

/-- Index containment of a cell in a grid rectangle. -/
def nCellIn (i j : ℕ) (r : GRect) : Bool := decide (r.1 ≤ i ∧ i < r.2.1 ∧ r.2.2.1 ≤ j ∧ j < r.2.2.2)

/-- Every cell of the box is a region cell or is missed by a line of the item. -/
def nSepB (al : List NLn) (seps : List ((ℕ × ℕ) × ℕ)) (b : ℕ × ℕ × ℕ × ℕ) : Bool :=
  (List.range' b.1 (b.2.1 - b.1)).all fun i => (List.range' b.2.2.1 (b.2.2.2 - b.2.2.1)).all fun j =>
    cnRR.any (nCellIn i j) ||
      (seps.lookup (i, j)).any fun m => decide (m < al.length) && offCellB (al.getD m (.f, .f)) (i, j)

/-- The leaf check. -/
def nLeafB (c : ℕ × ℕ) (cuts : List NLn) : NTree → Bool
  | .empty l => decide (l ∈ cuts) && emptyB l c
  | .leaf k ls w seps =>
    if k = 2 then decide (ls = pocketLns) && containB ls cuts c
    else if k = 3 then decide (ls = qLns) && containB ls cuts c
    else
      decide (k ≤ 1) && containB (ls ++ boxLns (nBox c (nGuardIdx k))) cuts c &&
        (ls ++ boxLns (nBox c (nGuardIdx k))).all
          (fun l => nnN (lnDet l (NRef.g (nGuardIdx k).1 (nGuardIdx k).2).mp)) &&
        (ls ++ boxLns (nBox c (nGuardIdx k))).all (fun l => posN (lnDet l (wpt w))) &&
        nSepB (ls ++ boxLns (nBox c (nGuardIdx k))) seps (nBox c (nGuardIdx k))
  | .lin _ _ _ => false

/-- The tree check. -/
def treeNB (c : ℕ × ℕ) : List NLn → NTree → Bool
  | cuts, .lin l t1 t2 => treeNB c (l :: cuts) t1 && treeNB c ((l.2, l.1) :: cuts) t2
  | cuts, t => nLeafB c cuts t

/-! ### Realisation -/

section Real

variable (xN H : ℝ) (xs : List ℝ)

/-- The real point of polynomial coordinates. -/
noncomputable def mpReal (p : MP × MP) : Point := (xN + MP.ev xs p.1, 2 * H + MP.ev xs p.2)

/-- The real point of a named point. -/
noncomputable def NRef.real (r : NRef) : Point := mpReal xN H xs r.mp

/-- The half-plane of a line. -/
def NLn.set (l : NLn) : Set Point := {z | 0 ≤ det (l.1.real xN H xs) (l.2.real xN H xs) z}

theorem mpDet_ev (u v z : MP × MP) :
    det (mpReal xN H xs u) (mpReal xN H xs v) (mpReal xN H xs z) = MP.ev xs (mpDet u v z) := by
  simp only [mpReal, det, mpDet, MP.ev_sub, MP.ev_mul]; ring

theorem lnDet_ev (l : NLn) (z : MP × MP) :
    det (l.1.real xN H xs) (l.2.real xN H xs) (mpReal xN H xs z) = MP.ev xs (lnDet l z) :=
  mpDet_ev xN H xs _ _ _

theorem NRef.real_g (i j : ℕ) : (NRef.g i j).real xN H xs = gpt (nφ xN xs) (nψ H xs) (i, j) := by
  simp [NRef.real, mpReal, NRef.mp, gpt, nφ, nψ]

theorem NLn.set_or (l : NLn) (z : Point) :
    z ∈ l.set xN H xs ∨ z ∈ NLn.set xN H xs (l.2, l.1) := by
  simp only [NLn.set, mem_ofPred_eq]
  rw [show det (l.2.real xN H xs) (l.1.real xN H xs) z = -det (l.1.real xN H xs) (l.2.real xN H xs) z
    by simp only [det]; ring]
  rcases le_total 0 (det (l.1.real xN H xs) (l.2.real xN H xs) z) with h | h
  · exact Or.inl h
  · exact Or.inr (by linarith)

theorem NLn.convex (l : NLn) : Convex ℝ (l.set xN H xs) := by
  intro a ha b hb s t hs ht hst
  simp only [NLn.set, mem_ofPred_eq] at ha hb ⊢
  rw [det_affine] at ha hb ⊢
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  have e : t = 1 - s := by linarith
  subst e
  nlinarith [mul_nonneg hs ha, mul_nonneg ht hb]

/-- The realised cell. -/
noncomputable def nCell (c : ℕ × ℕ) : Set Point :=
  (realR (nφ xN xs) (nψ H xs) (c.1, c.1 + 1, c.2, c.2 + 1)).set

end Real

variable {xN H : ℝ} {xs : List ℝ} (hxs : InDom nookDom xs)
  (hφ : StrictMonoOn (nφ xN xs) (Iio 20)) (hψ : StrictMonoOn (nψ H xs) (Iio 19))

include hxs in
theorem nnN_sound {p : MP} (h : nnN p = true) : 0 ≤ MP.ev xs p :=
  MP.ev_norm xs p ▸ MP.nnS_sound h hxs

include hxs in
theorem posN_sound {p : MP} (h : posN p = true) : 0 < MP.ev xs p :=
  MP.ev_norm xs p ▸ MP.posS_sound h hxs

/-- `det` with a line is affine in the point. -/
theorem lnDet_affine (l : NLn) : ∀ x y : ℝ, det (l.1.real xN H xs) (l.2.real xN H xs) (x, y) =
    (-((l.2.real xN H xs).2 - (l.1.real xN H xs).2)) * x +
      ((l.2.real xN H xs).1 - (l.1.real xN H xs).1) * y +
      (((l.2.real xN H xs).2 - (l.1.real xN H xs).2) * (l.1.real xN H xs).1 -
        ((l.2.real xN H xs).1 - (l.1.real xN H xs).1) * (l.1.real xN H xs).2) :=
  fun x y => det_affine _ _ (x, y)

theorem corner_real (c : ℕ × ℕ) :
    (NRef.g c.1 c.2).real xN H xs = (nφ xN xs c.1, nψ H xs c.2) ∧
    (NRef.g (c.1 + 1) c.2).real xN H xs = (nφ xN xs (c.1 + 1), nψ H xs c.2) ∧
    (NRef.g (c.1 + 1) (c.2 + 1)).real xN H xs = (nφ xN xs (c.1 + 1), nψ H xs (c.2 + 1)) ∧
    (NRef.g c.1 (c.2 + 1)).real xN H xs = (nφ xN xs c.1, nψ H xs (c.2 + 1)) := by
  simp only [NRef.real_g, gpt, and_self]

/-- `det` with a fixed line, bounded at the corners of a rectangle, is bounded on it. -/
theorem det_rect_nonneg {a b : Point} {x0 x1 y0 y1 : ℝ} (h00 : 0 ≤ det a b (x0, y0))
    (h10 : 0 ≤ det a b (x1, y0)) (h11 : 0 ≤ det a b (x1, y1)) (h01 : 0 ≤ det a b (x0, y1))
    {z : Point} (z1 : x0 ≤ z.1) (z2 : z.1 ≤ x1) (z3 : y0 ≤ z.2) (z4 : z.2 ≤ y1) :
    0 ≤ det a b z := by
  have := affine_rect (c := 0) (fun x y => det a b (x, y)) (fun x y => det_affine a b (x, y))
    h00 h10 h01 h11 z1 z2 z3 z4
  simpa using this

theorem det_rect_nonpos {a b : Point} {x0 x1 y0 y1 : ℝ} (h00 : det a b (x0, y0) ≤ 0)
    (h10 : det a b (x1, y0) ≤ 0) (h11 : det a b (x1, y1) ≤ 0) (h01 : det a b (x0, y1) ≤ 0)
    {z : Point} (z1 : x0 ≤ z.1) (z2 : z.1 ≤ x1) (z3 : y0 ≤ z.2) (z4 : z.2 ≤ y1) :
    det a b z ≤ 0 := by
  have h := det_rect_nonneg (a := b) (b := a) (by rw [det_swap12]; linarith)
    (by rw [det_swap12]; linarith) (by rw [det_swap12]; linarith) (by rw [det_swap12]; linarith)
    z1 z2 z3 z4
  rw [det_swap12] at h; linarith

theorem det_rect_neg {a b : Point} {x0 x1 y0 y1 : ℝ} (h00 : det a b (x0, y0) < 0)
    (h10 : det a b (x1, y0) < 0) (h11 : det a b (x1, y1) < 0) (h01 : det a b (x0, y1) < 0)
    {z : Point} (z1 : x0 ≤ z.1) (z2 : z.1 ≤ x1) (z3 : y0 ≤ z.2) (z4 : z.2 ≤ y1) :
    det a b z < 0 := by
  have := affine_pos_rect (fun x y => det b a (x, y)) (fun x y => det_affine b a (x, y))
    (by rw [det_swap12]; linarith) (by rw [det_swap12]; linarith) (by rw [det_swap12]; linarith)
    (by rw [det_swap12]; linarith) z1 z2 z3 z4
  simp only [Prod.mk.eta] at this
  rw [det_swap12] at this; linarith

include hxs in
/-- A line nonnegative at the corners of a cell is nonnegative on the cell. -/
theorem holdsB_sound {l : NLn} {c : ℕ × ℕ} (h : holdsB l c = true) {z : Point}
    (hz : z ∈ nCell xN H xs c) : z ∈ l.set xN H xs := by
  simp only [holdsB, cellCs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have v := fun (q : NRef) (hq : nnN (lnDet l q.mp) = true) =>
    (lnDet_ev xN H xs l q.mp).symm ▸ nnN_sound hxs hq
  obtain ⟨e1, e2, e3, e4⟩ := corner_real (xN := xN) (H := H) (xs := xs) c
  have a1 := v _ h1; have a2 := v _ h2; have a3 := v _ h3; have a4 := v _ h4
  simp only [NRef.real] at e1 e2 e3 e4
  rw [show mpReal xN H xs (NRef.g c.1 c.2).mp = _ from e1] at a1
  rw [show mpReal xN H xs (NRef.g (c.1 + 1) c.2).mp = _ from e2] at a2
  rw [show mpReal xN H xs (NRef.g (c.1 + 1) (c.2 + 1)).mp = _ from e3] at a3
  rw [show mpReal xN H xs (NRef.g c.1 (c.2 + 1)).mp = _ from e4] at a4
  obtain ⟨z1, z2, z3, z4⟩ := hz
  simp only [realR] at z1 z2 z3 z4
  exact det_rect_nonneg a1 a2 a3 a4 z1 z2 z3 z4

include hxs in
/-- A line `≤ 0` at the corners of a cell is `≤ 0` on the cell. -/
theorem offCellB_sound {l : NLn} {c : ℕ × ℕ} (h : offCellB l c = true) {z : Point}
    (hz : z ∈ nCell xN H xs c) : det (l.1.real xN H xs) (l.2.real xN H xs) z ≤ 0 := by
  simp only [offCellB, cellCs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have v := fun (q : NRef) (hq : nnN (MP.neg (lnDet l q.mp)) = true) => by
    have := nnN_sound hxs hq
    rw [MP.ev_neg, ← lnDet_ev xN H xs l q.mp] at this
    exact this
  obtain ⟨e1, e2, e3, e4⟩ := corner_real (xN := xN) (H := H) (xs := xs) c
  have a1 := v _ h1; have a2 := v _ h2; have a3 := v _ h3; have a4 := v _ h4
  simp only [NRef.real] at e1 e2 e3 e4
  rw [show mpReal xN H xs (NRef.g c.1 c.2).mp = _ from e1] at a1
  rw [show mpReal xN H xs (NRef.g (c.1 + 1) c.2).mp = _ from e2] at a2
  rw [show mpReal xN H xs (NRef.g (c.1 + 1) (c.2 + 1)).mp = _ from e3] at a3
  rw [show mpReal xN H xs (NRef.g c.1 (c.2 + 1)).mp = _ from e4] at a4
  obtain ⟨z1, z2, z3, z4⟩ := hz
  simp only [realR] at z1 z2 z3 z4
  exact det_rect_nonpos (by linarith) (by linarith) (by linarith) (by linarith) z1 z2 z3 z4

include hxs in
/-- A line `< 0` at the corners of a cell is `< 0` on the cell. -/
theorem emptyB_sound {l : NLn} {c : ℕ × ℕ} (h : emptyB l c = true) {z : Point}
    (hz : z ∈ nCell xN H xs c) : det (l.1.real xN H xs) (l.2.real xN H xs) z < 0 := by
  simp only [emptyB, cellCs, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have v := fun (q : NRef) (hq : posN (MP.neg (lnDet l q.mp)) = true) => by
    have := posN_sound hxs hq
    rw [MP.ev_neg, ← lnDet_ev xN H xs l q.mp] at this
    exact this
  obtain ⟨e1, e2, e3, e4⟩ := corner_real (xN := xN) (H := H) (xs := xs) c
  have a1 := v _ h1; have a2 := v _ h2; have a3 := v _ h3; have a4 := v _ h4
  simp only [NRef.real] at e1 e2 e3 e4
  rw [show mpReal xN H xs (NRef.g c.1 c.2).mp = _ from e1] at a1
  rw [show mpReal xN H xs (NRef.g (c.1 + 1) c.2).mp = _ from e2] at a2
  rw [show mpReal xN H xs (NRef.g (c.1 + 1) (c.2 + 1)).mp = _ from e3] at a3
  rw [show mpReal xN H xs (NRef.g c.1 (c.2 + 1)).mp = _ from e4] at a4
  obtain ⟨z1, z2, z3, z4⟩ := hz
  simp only [realR] at z1 z2 z3 z4
  exact det_rect_neg (by linarith) (by linarith) (by linarith) (by linarith) z1 z2 z3 z4

include hxs in
theorem containB_sound {ls cuts : List NLn} {c : ℕ × ℕ} (h : containB ls cuts c = true)
    {z : Point} (hz : z ∈ nCell xN H xs c) (hcut : ∀ l ∈ cuts, z ∈ l.set xN H xs) :
    ∀ l ∈ ls, z ∈ l.set xN H xs := by
  intro l hl
  have := List.all_eq_true.1 h l hl
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  rcases this with h1 | h1
  · exact hcut l h1
  · exact holdsB_sound hxs h1 hz


/-! ### Items -/

/-- A point between the entries `a` and `a + k + 1` of a sequence lies between two consecutive
entries. -/
theorem nexists_step {f : ℕ → ℝ} {x : ℝ} :
    ∀ (k a : ℕ), f a ≤ x → x ≤ f (a + k + 1) → ∃ i, a ≤ i ∧ i ≤ a + k ∧ f i ≤ x ∧ x ≤ f (i + 1)
  | 0, a, h1, h2 => ⟨a, le_rfl, by omega, h1, by simpa using h2⟩
  | k + 1, a, h1, h2 => by
    by_cases hx : x ≤ f (a + 1)
    · exact ⟨a, le_rfl, by omega, h1, hx⟩
    · have e : a + 1 + k + 1 = a + (k + 1) + 1 := by omega
      have h2' : x ≤ f (a + 1 + k + 1) := by rw [e]; exact h2
      obtain ⟨i, hi1, hi2, hi3, hi4⟩ := nexists_step k (a + 1) (le_of_lt (not_le.1 hx)) h2'
      exact ⟨i, by omega, by omega, hi3, hi4⟩

/-- The item of a list of lines. -/
def nItem (xN H : ℝ) (xs : List ℝ) (al : List NLn) : Set Point := {z | ∀ l ∈ al, z ∈ l.set xN H xs}

theorem nItem_convex (al : List NLn) : Convex ℝ (nItem xN H xs al) := by
  intro a ha b hb s t hs ht hst l hl
  exact NLn.convex xN H xs l (ha l hl) (hb l hl) hs ht hst

/-- **Closure argument**: an item with a strict point, whose strict points lie in a closed set,
lies in it. -/
theorem nItem_sub {al : List NLn} {S : Set Point} (hS : IsClosed S) {p0 : Point}
    (hp0 : ∀ l ∈ al, 0 < det (l.1.real xN H xs) (l.2.real xN H xs) p0)
    (hst : ∀ q : Point, (∀ l ∈ al, 0 < det (l.1.real xN H xs) (l.2.real xN H xs) q) → q ∈ S) :
    nItem xN H xs al ⊆ S := by
  intro z hz
  have ht : Filter.Tendsto (fun n : ℕ => z + (1 / ((n : ℝ) + 1)) • (p0 - z)) Filter.atTop
      (nhds (z + (0 : ℝ) • (p0 - z))) :=
    tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.smul_const _)
  rw [zero_smul, add_zero] at ht
  refine hS.mem_of_tendsto ht (Filter.Eventually.of_forall fun n => hst _ fun l hl => ?_)
  set t : ℝ := 1 / ((n : ℝ) + 1)
  have ht0 : 0 < t := by positivity
  have ht1 : t ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have a := hz l hl
  have b := hp0 l hl
  simp only [NLn.set, mem_ofPred_eq] at a
  rw [det_affine] at a b ⊢
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub,
    Prod.snd_sub, smul_eq_mul]
  have h1t : 0 ≤ 1 - t := by linarith
  nlinarith [mul_nonneg h1t a, mul_pos ht0 b]

/-- The region cells are well formed. -/
theorem cnRR_bnd : ∀ r ∈ cnRR, r.2.1 < 20 ∧ r.2.2.2 < 19 := by decide

include hxs hφ hψ in
/-- **Strict points of an item lie in the region**: they lie in a cell of the box, which is a
region cell or is missed by a line of the item. -/
theorem nItem_strict {al : List NLn} {seps : List ((ℕ × ℕ) × ℕ)} {b : ℕ × ℕ × ℕ × ℕ}
    (hsep : nSepB al seps b = true) (hb : b.1 < b.2.1 ∧ b.2.1 < 20 ∧ b.2.2.1 < b.2.2.2 ∧ b.2.2.2 < 19)
    (hbox : ∀ l ∈ boxLns b, l ∈ al) {S : Set Point}
    (hreg : ∀ r ∈ cnRR, (realR (nφ xN xs) (nψ H xs) r).set ⊆ S) {q : Point}
    (hq : ∀ l ∈ al, 0 < det (l.1.real xN H xs) (l.2.real xN H xs) q) : q ∈ S := by
  obtain ⟨b0, b1, b2, b3⟩ := b
  obtain ⟨h01, h1, h23, h3⟩ := hb
  simp only at h01 h1 h23 h3
  have mφ : ∀ a c, a ≤ c → c < 20 → nφ xN xs a ≤ nφ xN xs c := fun a c hac hc =>
    (hφ.le_iff_le (show a ∈ Iio 20 from lt_of_le_of_lt hac hc) hc).2 hac
  have mψ : ∀ a c, a ≤ c → c < 19 → nψ H xs a ≤ nψ H xs c := fun a c hac hc =>
    (hψ.le_iff_le (show a ∈ Iio 19 from lt_of_le_of_lt hac hc) hc).2 hac
  have sφ : nφ xN xs b0 < nφ xN xs b1 := hφ (show b0 ∈ Iio 20 by simp; omega) h1 h01
  have sψ : nψ H xs b2 < nψ H xs b3 := hψ (show b2 ∈ Iio 19 by simp; omega) h3 h23
  -- the box sides
  have hb' := fun i (hi : i < 4) => hq _ (hbox _ (List.getElem_mem (l := boxLns (b0, b1, b2, b3))
    (by simp [boxLns]; omega)))
  have c1 := hb' 0 (by norm_num)
  have c2 := hb' 1 (by norm_num)
  have c3 := hb' 2 (by norm_num)
  have c4 := hb' 3 (by norm_num)
  simp only [boxLns, List.getElem_cons_zero, List.getElem_cons_succ, NRef.real_g, gpt, det] at c1 c2 c3 c4
  have q2 : nψ H xs b2 < q.2 := by nlinarith
  have q1 : q.1 < nφ xN xs b1 := by nlinarith
  have q4 : q.2 < nψ H xs b3 := by nlinarith
  have q3 : nφ xN xs b0 < q.1 := by nlinarith
  -- the cell of `q`
  have ex : b0 + (b1 - b0 - 1) + 1 = b1 := by omega
  have ey : b2 + (b3 - b2 - 1) + 1 = b3 := by omega
  obtain ⟨i, hi1, hi2, hxi, hxi'⟩ := nexists_step (f := nφ xN xs) (b1 - b0 - 1) b0 q3.le
    (by rw [ex]; exact q1.le)
  obtain ⟨j, hj1, hj2, hyj, hyj'⟩ := nexists_step (f := nψ H xs) (b3 - b2 - 1) b2 q2.le
    (by rw [ey]; exact q4.le)
  have hs := List.all_eq_true.1 (List.all_eq_true.1 hsep i (List.mem_range'_1.2 ⟨by dsimp only; omega, by dsimp only; omega⟩)) j
    (List.mem_range'_1.2 ⟨by dsimp only; omega, by dsimp only; omega⟩)
  simp only [Bool.or_eq_true, List.any_eq_true, Option.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at hs
  have hqc : q ∈ nCell xN H xs (i, j) := ⟨hxi, hxi', hyj, hyj'⟩
  rcases hs with ⟨r, hr, hri⟩ | ⟨m, -, hm, hoff⟩
  · apply hreg r hr
    simp only [nCellIn, decide_eq_true_eq] at hri
    obtain ⟨r1, r2, r3, r4⟩ := hri
    obtain ⟨w1, w2⟩ := cnRR_bnd r hr
    refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [realR]
    · exact (mφ _ _ r1 (by omega)).trans hxi
    · exact hxi'.trans (mφ _ _ r2 w1)
    · exact (mψ _ _ r3 (by omega)).trans hyj
    · exact hyj'.trans (mψ _ _ r4 w2)
  · exfalso
    have h1 := offCellB_sound hxs hoff hqc
    have h2 := hq _ (List.getD_eq_getElem (l := al) (d := (.f, .f)) hm ▸ List.getElem_mem hm)
    linarith

/-- The guard point of a guard leaf. -/
noncomputable def nGuardPt (xN H : ℝ) (xs : List ℝ) (k : ℕ) : Point :=
  (NRef.g (nGuardIdx k).1 (nGuardIdx k).2).real xN H xs

theorem nBox_ok {c : ℕ × ℕ} (hc : c.1 + 1 < 20 ∧ c.2 + 1 < 19) (k : ℕ) :
    (nBox c (nGuardIdx k)).1 < (nBox c (nGuardIdx k)).2.1 ∧ (nBox c (nGuardIdx k)).2.1 < 20 ∧
      (nBox c (nGuardIdx k)).2.2.1 < (nBox c (nGuardIdx k)).2.2.2 ∧
      (nBox c (nGuardIdx k)).2.2.2 < 19 := by
  have hg : (nGuardIdx k).1 < 20 ∧ (nGuardIdx k).2 < 19 := by
    unfold nGuardIdx; split <;> simp
  simp only [nBox]
  omega

include hxs hφ hψ in
/-- **A guard leaf**: the guard sees every point of the leaf within the item. -/
theorem nleaf_guard_sound {c : ℕ × ℕ} {cuts : List NLn} {k : ℕ} {ls : List NLn}
    {w : List (ℚ × NRef)} {seps : List ((ℕ × ℕ) × ℕ)}
    (h : nLeafB c cuts (.leaf k ls w seps) = true) (hk2 : k ≠ 2) (hk3 : k ≠ 3)
    (hc : c.1 + 1 < 20 ∧ c.2 + 1 < 19) {S : Set Point} (hS : IsClosed S)
    (hreg : ∀ r ∈ cnRR, (realR (nφ xN xs) (nψ H xs) r).set ⊆ S) {z : Point}
    (hz : z ∈ nCell xN H xs c) (hcut : ∀ l ∈ cuts, z ∈ l.set xN H xs) :
    k ≤ 1 ∧ ArtGallery.segment (nGuardPt xN H xs k) z ⊆ S := by
  simp only [nLeafB, hk2, hk3, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hk, hcont⟩, hguard⟩, hinner⟩, hsep⟩ := h
  refine ⟨hk, ?_⟩
  set al := ls ++ boxLns (nBox c (nGuardIdx k))
  have hI : nItem xN H xs al ⊆ S := by
    refine nItem_sub hS (p0 := mpReal xN H xs (wpt w)) (fun l hl => ?_) (fun q hq =>
      nItem_strict hxs hφ hψ hsep (nBox_ok hc k) (fun l hl => List.mem_append_right _ hl) hreg hq)
    rw [lnDet_ev]; exact posN_sound hxs (List.all_eq_true.1 hinner l hl)
  have hg : nGuardPt xN H xs k ∈ nItem xN H xs al := by
    intro l hl
    change 0 ≤ det (l.1.real xN H xs) (l.2.real xN H xs)
      (mpReal xN H xs (NRef.g (nGuardIdx k).1 (nGuardIdx k).2).mp)
    rw [lnDet_ev]; exact nnN_sound hxs (List.all_eq_true.1 hguard l hl)
  have hzI : z ∈ nItem xN H xs al := containB_sound hxs hcont hz hcut
  intro p hp
  rw [segment_eq] at hp
  exact hI ((nItem_convex al).segment_subset hg hzI hp)

/-- The pocket. -/
def nPocket (xN H : ℝ) (xs : List ℝ) : Set Point := nItem xN H xs pocketLns

/-- The triangle `Q`. -/
def nQ (xN H : ℝ) (xs : List ℝ) : Set Point := nItem xN H xs qLns

include hxs hφ hψ in
/-- **Soundness of a cut tree.** -/
theorem treeNB_sound {c : ℕ × ℕ} (hc : c.1 + 1 < 20 ∧ c.2 + 1 < 19) {S : Set Point}
    (hS : IsClosed S) (hreg : ∀ r ∈ cnRR, (realR (nφ xN xs) (nψ H xs) r).set ⊆ S) {z : Point}
    (hz : z ∈ nCell xN H xs c) :
    ∀ (t : NTree) (cuts : List NLn), treeNB c cuts t = true → (∀ l ∈ cuts, z ∈ l.set xN H xs) →
      (∃ k ≤ 1, ArtGallery.segment (nGuardPt xN H xs k) z ⊆ S) ∨ z ∈ nPocket xN H xs ∨
        z ∈ nQ xN H xs
  | .lin l t1 t2, cuts, h, hcut => by
    simp only [treeNB, Bool.and_eq_true] at h
    rcases NLn.set_or xN H xs l z with hl | hl
    · exact treeNB_sound hc hS hreg hz t1 (l :: cuts) h.1 (fun l' hl' => by
        rcases List.mem_cons.1 hl' with rfl | hl'
        · exact hl
        · exact hcut l' hl')
    · exact treeNB_sound hc hS hreg hz t2 ((l.2, l.1) :: cuts) h.2 (fun l' hl' => by
        rcases List.mem_cons.1 hl' with rfl | hl'
        · exact hl
        · exact hcut l' hl')
  | .empty l, cuts, h, hcut => by
    simp only [treeNB, nLeafB, Bool.and_eq_true, decide_eq_true_eq] at h
    exfalso
    have h1 := emptyB_sound hxs h.2 hz
    have h2 := hcut l h.1
    simp only [NLn.set, mem_ofPred_eq] at h2
    linarith
  | .leaf k ls w seps, cuts, h, hcut => by
    have h' : nLeafB c cuts (.leaf k ls w seps) = true := h
    by_cases hk2 : k = 2
    · subst hk2
      simp only [nLeafB, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at h'
      obtain ⟨rfl, hc'⟩ := h'
      exact Or.inr (Or.inl (containB_sound hxs hc' hz hcut))
    by_cases hk3 : k = 3
    · subst hk3
      simp only [nLeafB, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
        show (3 : ℕ) ≠ 2 by norm_num] at h'
      obtain ⟨rfl, hc'⟩ := h'
      exact Or.inr (Or.inr (containB_sound hxs hc' hz hcut))
    obtain ⟨hk, hseg⟩ := nleaf_guard_sound hxs hφ hψ h' hk2 hk3 hc hS hreg hz hcut
    exact Or.inl ⟨k, hk, hseg⟩

end

end ArtGallery.Orthogonal.Hard
