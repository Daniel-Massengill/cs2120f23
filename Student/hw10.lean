-- 1. Every dog likes some cat.
variable (Dog : Type) (Cat : Type) (Likes : Dog → Cat → Prop)

#check ∀ (d : Dog), ∃ (c : Cat), Likes d c

-- 2. If any dog, d, likes any dog, g, and that dog, g, likes any dog, w, then d likes w.
variable (Likes : Dog → Dog → Prop)
#check ∀ (d g w : Dog), Likes d g → Likes g w → Likes d w

-- 3. If any cat, c, likes any cat, d, then d also likes c.
variable (Likes : Cat → Cat → Prop)

#check ∀ (c d : Cat), (∃ (e : Cat), Likes c e) → Likes d c

-- 4. Every cat, c, likes itself.
variable (Likes : Cat → Cat → Prop)

#check ∀ (c : Cat), Likes c c

-- 5. If every cat likes every other cat, and c and d are cats, then c likes d.
variable (LikesAll : Cat → Cat → Prop)

#check ∀ (c d : Cat), (∀ (e : Cat), LikesAll c e) → LikesAll d c → Likes c d


-- Formal proof for proposition #5:

example :
  ∀ (c d : Cat), (∀ (e : Cat), LikesAll c e) → LikesAll d c → Likes c d :=
fun c d h1 h2, h1 d h2
