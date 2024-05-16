import Mathlib.Data.Real.Basic

namespace hilbert

---------------
def Point := Type
def Line := Type


--relations
-- def lies_on_L (a : Point) (l : Line) := True
axiom lies_on_L (a : Point) (l : Line) : Prop


axiom distinct_points : ∀ p : Point , ∃q: Point, p ≠ q

-- I. 1 : line from two points
axiom line {a b: Point} (nab : a ≠ b) : Line


-- I. 2 : for every two points there exists a distinct line
--existence of line for any two distinct points
axiom line_exists{a b : Point} (nab : a ≠ b) : ∃ l : Line, lies_on_L a l ∧ lies_on_L b l

-- determine same line
axiom same_line {l : Line} {a b : Point} {nab: a ≠ b} {h: lies_on_L a l ∧ lies_on_L b l} : l = (line nab)


-- I.3 : exists 2 points on a line, there exists atleast 3 points not on a line
axiom points_exist_on_line (l : Line) : ∃ a b : Point, lies_on_L a l ∧ lies_on_L b l ∧ a ≠ b

-- collinear points
def collinear := fun a b c: Point => ∃ l: Line, (lies_on_L a l) ∧ (lies_on_L b l) ∧ (lies_on_L c l)

-- exists non_collinear points
axiom non_collinear : ∃(a b c: Point), a ≠ b ∧ a ≠ b ∧ b ≠ c ∧ ¬(collinear a b c)


-- Group II: axiom of order

axiom between : Point → Point → Point → Prop
-- II1:
axiom between_distinct_points {a b c : Point} :
  between a b c →
  a ≠ b ∧ a ≠ c ∧ b ≠ c

axiom between_line_exists {a b c : Point}:
  between a b c →
  ∃ l : Line, lies_on_L a l ∧ lies_on_L b l ∧ lies_on_L c l

axiom between_sym {a b c : Point} : between a b c → between c b a

-- II 2: For two points a and b, there exists atleast one point c such that b lies between a c
axiom between_extend {a b : Point} (h: a ≠ b):
  ∃ c: Point , between a b c

-- II 3: of any three points on a line there exists no more than one that lies between the other two
axiom exist_unique_point_between {a b c : Point} :
  between a b c  →
  ¬ between a c b ∧ ¬ between b a c

-- II 4 : Pasch's axiom
def intersect_line_segment: Line → Point→ Point → Prop:= fun l a b => ∃ c:Point, (lies_on_L c l) ∧ (between a c b)
  ∧ ¬ (lies_on_L a l) ∧ ¬ (lies_on_L b l)

axiom Pasch {a b c: Point} {l: Line} :
  ¬(collinear a b c) → (intersect_line_segment l a b) → ¬(lies_on_L c l) →
   (intersect_line_segment l a c) ∨ (intersect_line_segment l b c)


-- Axiom III.1

axiom cong (a b a' b' : Point): Prop
axiom cong_exist (a b o: Point) (l: Line) (nab: a ≠ b) : lies_on_L o l →
∃ a' b':Point , lies_on_L a' l ∧ lies_on_L b' l ∧ between a' o b' ∧ cong a b o a' ∧ cong a b o b'

axiom cong_permute (a b c d: Point) : cong a b c d → cong a b d c



-- Axiom III.2
-- if two segments are congruent to a third one they are congruent to each other


axiom cong_transitive1 (a b a' b' a'' b'': Point) :
  cong a b a' b' → cong a b a'' b'' → cong a' b' a'' b''

axiom cong_transitive2 (a b a' b' a'' b'': Point) :
  cong a b a' b' → cong a'' b'' a b → cong a' b' a'' b''

--Axiom III.3
def disjoint := fun a b c d=> ¬ ∃ p, between a p b ∧ between c p d

axiom add_segment (a b c a' b' c' : Point) :
  between a b c →
  between a' b' c' →
  disjoint a b b c →
  disjoint a' b' b' c' →
  cong a b a' b' ∧ cong b c b' c' →
   cong a c a' c'


--Axiom III.4
-- angle l m and angle m l are the same


-- III 4. existence of congruent angle
axiom congA (a b c a' b' c' : Point) : Prop



-- implied construction
axiom angle_reflex (a b c : Point) (h : ¬ collinear a b c): congA a b c a b c
axiom angle_comm (a b c : Point) (h : ¬ collinear a b c): congA a b c c b a

-- symmetry is also implied
axiom congA_symm {a b c a' b' c':Point} :
  congA a b c a' b' c' →
  congA a' b' c' a b c

-- permutation from different construction with rays
-- implied in definition
axiom congA_perm2 {a b c a' b' c':Point} :
  congA a b c a' b' c' →
  congA c b a c' b' a'

-- one can also briefly say that a unique angle can be constructed from a ray.
-- 2 different rays with the same verex determines a angle.

--can be proved
-- axiom congAH_reflex {a b c :Point} : ¬ collinear a b c -> congA a b c a b c


def Same_side_plane  (l : Line) (a b : Point) := ∃ p:Point, intersect_line_segment l a p ∧ intersect_line_segment l b p
def same_side_plane' := fun a b a' b' => forall l : Line, lies_on_L a l → lies_on_L b l → Same_side_plane l a' b'

def same_side_ray :=
  fun o a b : Point =>
    between o a b ∨ between o b a ∨ ( o ≠ a ∧ a = b)

--angle exists
-- ¬ collinear a' b' p' might be provable

axiom angle (o a b x y : Point) : ¬ collinear o a b ∧ same_side_ray o a x ∧ same_side_ray o b y <-> congA a o b x o y

axiom angle_exists :
   ∀ a b c a' b' c',
     ¬ collinear a b c → ¬ collinear a' b' c' →
     ∃ c'', congA a b c a' b' c'' ∧ same_side_plane' c c'' b' a' ∧ ¬ collinear a' b' c''

-- determining angle from ray
axiom angle_rays (a b c x y z a' c' x' z' : Point) :
    congA a b c x y z →
    same_side_ray b a a' → same_side_ray b c c' →
    same_side_ray y x x' → same_side_ray y z z' →
    congA a' b c' x' y z'




-- unique angle
-- if angle abc is congruent to angle abc', then c and c' are on the same side. of the ray emanating form b,
-- this determines unique ray because p p' lie in the same side of ray from point b.

axiom angle_unique (a b c a' b' c' p p' : Point):
     ¬ collinear a b c → ¬ collinear a' b' c' →
     congA a b c a' b' p → congA a b c a' b' p' →
     same_side_plane' c' p a' b' → same_side_plane' c' p' a' b' →
     same_side_ray b p p'

-- axiom III. 5
axiom congA5 {a b c a' b' c':Point} :
  ¬ collinear a b c →
  ¬ collinear a' b' c' →
  cong b a b' a' →
  cong a c a' c' →
  congA b a c b' a' c' →
  congA a b c a' b' c'


--can be proven?
axiom cong_unicity (a b x a' b' a'' b'': Point) (l m : Line) (nab : a ≠ b) :
  lies_on_L a' l → lies_on_L b' l →
  between a'  x  b' → cong x a' a b → cong x b' a b ->
  lies_on_L a'' l → lies_on_L b'' l →
  between a'' x b'' → cong x a'' a b → cong x b'' a b →
  (a' = a'' ∧ b' = b'') ∨ (a' = b'' ∧ b' = a'')
