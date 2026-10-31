module

public import ArtGallery.Orthogonal.Hard.RectGen

/-!
# Zones: certified rectangle decompositions on a grid

A *zone* is a part of the region of an orthogonal polygon near one feature, decomposed into
rectangles (a vertical decomposition computed during development).  Its data is
given on a **grid**: every coordinate is an index into a strictly increasing list of abscissae
or of ordinates; the realisation maps `φ` (abscissae) and `ψ` (ordinates) are only required to
be strictly increasing on the indices used.  The Boolean check `zoneOK` is evaluated by
`decide` on the indices; `zone_sound` turns it into geometric facts about the realised
rectangles:

* every rectangle is a convex piece;
* every point of every side of every rectangle lies on one of the listed boundary segments
  (`pedges`), or is an interior point of the union of the rectangles, or lies on the top or a
  lateral side of the zone's box;
* the top side of the box is tiled by rectangle tops, the lateral sides of the box are sides of
  the first and the last rectangle, and every listed boundary segment is covered by the
  rectangles.

Certificates: every rectangle's bottom lies on a boundary segment, its top on a boundary
segment or on the box top, and each lateral side is split into items, each lying on a boundary
segment or along a side of a neighbouring rectangle (two half-planes), with the breakpoints on
boundary segments.
-/

namespace ArtGallery.Orthogonal.Hard

@[expose] public section

open ArtGallery.Stade Set Metric

/-! ### Data -/

/-- A sub-interval of a lateral rectangle side lies on a boundary segment (`edge e`) or along the
side of the neighbouring rectangle `k` (`rect k`). -/
inductive VItem where
  | edge (e : ℕ)
  | rect (k : ℕ)
  deriving DecidableEq

/-- A grid rectangle `(x₀, x₁, y₀, y₁)`. -/
abbrev GRect := ℕ × ℕ × ℕ × ℕ

/-- A grid segment. -/
abbrev GSeg := (ℕ × ℕ) × (ℕ × ℕ)

/-- The certificate of a lateral side: items from bottom to top and the boundary segments of the
breakpoints between consecutive items; `none` for a side on the box. -/
abbrev SideCert := Option (List (ℕ × ℕ × VItem) × List ℕ)

/-- A zone. -/
structure Zone where
  /-- Number of abscissae / ordinates of the grid. -/
  NX : ℕ
  /-- Number of ordinates of the grid. -/
  NY : ℕ
  /-- The box: left, right abscissa, floor and top ordinate. -/
  L : ℕ
  /-- Right side of the box. -/
  R : ℕ
  /-- Floor of the box (the lateral box sides run from `F` to `T`). -/
  F : ℕ
  /-- Top of the box. -/
  T : ℕ
  /-- The rectangles. -/
  rects : List GRect
  /-- The boundary segments. -/
  pedges : List GSeg
  /-- The boundary segment of each rectangle's bottom. -/
  bot : List ℕ
  /-- The boundary segment of each rectangle's top (`none`: on the box top). -/
  top : List (Option ℕ)
  /-- The certificates of the left sides. -/
  left : List SideCert
  /-- The certificates of the right sides. -/
  right : List SideCert
  /-- The rectangles whose tops tile the box top, from left to right. -/
  topTiles : List ℕ
  /-- For every boundary segment, rectangles covering it in order. -/
  cover : List (List ℕ)

/-! ### Checks -/

/-- `a` lies between `b` and `c`. -/
def betweenB (a b c : ℕ) : Bool := (b ≤ a && a ≤ c) || (c ≤ a && a ≤ b)

/-- The grid point `p` lies on the axis-parallel grid segment `e`. -/
def onSegB (p : ℕ × ℕ) (e : GSeg) : Bool :=
  (e.1.1 == e.2.1 && p.1 == e.1.1 && betweenB p.2 e.1.2 e.2.2) ||
  (e.1.2 == e.2.2 && p.2 == e.1.2 && betweenB p.1 e.1.1 e.2.1)

/-- The default rectangle. -/
def GRect.default : GRect := (0, 0, 0, 0)

/-- An item of a lateral side at abscissa `x` (`isLeft`: the side is a left side). -/
def itemOK (z : Zone) (x : ℕ) (isLeft : Bool) (it : ℕ × ℕ × VItem) : Bool :=
  decide (it.1 < it.2.1) &&
  match it.2.2 with
  | .edge e => decide (e < z.pedges.length) && onSegB (x, it.1) (z.pedges.getD e ((0, 0), (0, 0))) &&
      onSegB (x, it.2.1) (z.pedges.getD e ((0, 0), (0, 0)))
  | .rect k =>
    let r := z.rects.getD k GRect.default
    decide (k < z.rects.length) && (if isLeft then r.2.1 == x else r.1 == x) &&
      decide (r.1 < r.2.1) && decide (r.2.2.1 ≤ it.1) && decide (it.2.1 ≤ r.2.2.2)

/-- The items run from `c` to `d`, consecutively. -/
def chainItems : ℕ → List (ℕ × ℕ × VItem) → ℕ → Bool
  | _, [], _ => false
  | c, [it], d => it.1 == c && it.2.1 == d
  | c, it :: rest, d => it.1 == c && chainItems it.2.1 rest d

/-- The breakpoints (upper ends of all items but the last) lie on the given segments. -/
def bpsOK (z : Zone) (x : ℕ) : List (ℕ × ℕ × VItem) → List ℕ → Bool
  | [], [] => true
  | [_], [] => true
  | it :: rest@(_ :: _), e :: es =>
    decide (e < z.pedges.length) && onSegB (x, it.2.1) (z.pedges.getD e ((0, 0), (0, 0))) &&
      bpsOK z x rest es
  | _, _ => false

/-- The check of a lateral side. -/
def sideOK (z : Zone) (r : GRect) (isLeft : Bool) (s : SideCert) : Bool :=
  let x := if isLeft then r.1 else r.2.1
  match s with
  | none => x == (if isLeft then z.L else z.R) && r.2.2.1 == z.F && r.2.2.2 == z.T
  | some (items, bps) => chainItems r.2.2.1 items r.2.2.2 && items.all (itemOK z x isLeft) &&
      bpsOK z x items bps

/-- The check of a rectangle top: on a boundary segment, or on the box top. -/
def topOK (z : Zone) (r : GRect) : Option ℕ → Bool
  | some t => decide (t < z.pedges.length) &&
      onSegB (r.1, r.2.2.2) (z.pedges.getD t ((0, 0), (0, 0))) &&
      onSegB (r.2.1, r.2.2.2) (z.pedges.getD t ((0, 0), (0, 0)))
  | none => r.2.2.2 == z.T && decide (z.L ≤ r.1) && decide (r.2.1 ≤ z.R)

/-- The check of rectangle `k`. -/
def rectOK (z : Zone) (k : ℕ) : Bool :=
  let r := z.rects.getD k GRect.default
  let e := z.pedges.getD (z.bot.getD k 0) ((0, 0), (0, 0))
  decide (r.1 < r.2.1) && decide (r.2.2.1 < r.2.2.2) && decide (r.2.1 < z.NX) &&
  decide (r.2.2.2 < z.NY) && decide (z.bot.getD k 0 < z.pedges.length) &&
  decide (z.L ≤ r.1 ∧ r.2.1 ≤ z.R ∧ r.2.2.2 ≤ z.T) &&
  onSegB (r.1, r.2.2.1) e && onSegB (r.2.1, r.2.2.1) e &&
  topOK z r (z.top.getD k none) &&
  sideOK z r true (z.left.getD k none) && sideOK z r false (z.right.getD k none)

/-- The tiles of the box top run from `c` to `d`. -/
def tilesOK (z : Zone) : ℕ → List ℕ → ℕ → Bool
  | _, [], _ => false
  | c, k :: rest, d =>
    let r := z.rects.getD k GRect.default
    decide (k < z.rects.length) && r.1 == c && r.2.2.2 == z.T &&
      (if rest = [] then r.2.1 == d else tilesOK z r.2.1 rest d)

/-- The intervals cover `[lo, hi]` in order. -/
def coverRun : List (ℕ × ℕ) → ℕ → ℕ → Bool
  | [], _, _ => false
  | i :: rest, lo, hi => decide (i.1 ≤ lo) && (decide (hi ≤ i.2) || coverRun rest i.2 hi)

/-- The rectangles `ks` cover the vertical segment `{x} × [lo, hi]`. -/
def coverV (z : Zone) (x lo hi : ℕ) (ks : List ℕ) : Bool :=
  ks.all (fun k => decide (k < z.rects.length) && decide ((z.rects.getD k GRect.default).1 ≤ x) &&
    decide (x ≤ (z.rects.getD k GRect.default).2.1)) &&
  coverRun (ks.map fun k => ((z.rects.getD k GRect.default).2.2.1,
    (z.rects.getD k GRect.default).2.2.2)) lo hi

/-- The rectangles `ks` cover the horizontal segment `[lo, hi] × {y}`. -/
def coverH (z : Zone) (y lo hi : ℕ) (ks : List ℕ) : Bool :=
  ks.all (fun k => decide (k < z.rects.length) &&
    decide ((z.rects.getD k GRect.default).2.2.1 ≤ y) &&
    decide (y ≤ (z.rects.getD k GRect.default).2.2.2)) &&
  coverRun (ks.map fun k => ((z.rects.getD k GRect.default).1,
    (z.rects.getD k GRect.default).2.1)) lo hi

/-- The rectangles `ks` cover the axis-parallel boundary segment `e`. -/
def coverOK (z : Zone) (e : GSeg) (ks : List ℕ) : Bool :=
  if e.1.1 = e.2.1 then coverV z e.1.1 (min e.1.2 e.2.2) (max e.1.2 e.2.2) ks
  else if e.1.2 = e.2.2 then coverH z e.1.2 (min e.1.1 e.2.1) (max e.1.1 e.2.1) ks
  else false

/-- **The zone check.** -/
def zoneOK (z : Zone) : Bool :=
  z.bot.length == z.rects.length && z.top.length == z.rects.length &&
  z.left.length == z.rects.length && z.right.length == z.rects.length &&
  z.cover.length == z.pedges.length &&
  z.pedges.all (fun e => decide (e.1.1 < z.NX ∧ e.2.1 < z.NX ∧ e.1.2 < z.NY ∧ e.2.2 < z.NY)) &&
  decide (z.L < z.NX ∧ z.R < z.NX ∧ z.F < z.NY ∧ z.T < z.NY) &&
  decide (0 < z.rects.length) && z.left.getD 0 (some ([], [])) == none &&
  z.right.getD (z.rects.length - 1) (some ([], [])) == none &&
  (List.range z.rects.length).all (rectOK z) &&
  tilesOK z z.L z.topTiles z.R &&
  (List.range z.pedges.length).all (fun e => coverOK z (z.pedges.getD e ((0, 0), (0, 0)))
    (z.cover.getD e []))

end

end ArtGallery.Orthogonal.Hard
