; Certified Manacher over the persistent Nat trie from self/base.sl.
; See pal/README.md for load order, cost model, and proof organization.

(def-adts
  ((ManCut : ((List (Nat)) xs) -> Type) enum
    (many MkManCut : (erased (List (Nat)) xs) (many (Nat) i)
      (many (List (Nat)) left right) (erased (PalCut xs i left right) p) -> (ManCut xs)))
  ((ManCutAt : ((List (Nat)) xs) ((Nat) i) -> Type) enum
    (many MkManCutAt : (erased (List (Nat)) xs) (erased (Nat) i)
      (many (List (Nat)) left right) (erased (PalCut xs i left right) p) -> (ManCutAt xs i)))
  ((ManSpan : ((List (Nat)) xs) -> Type) enum
    (many MkManSpan : (erased (List (Nat)) xs w) (many (Nat) lo hi radius width)
      (erased (PalRange xs lo hi w) range) (erased (Palindrome (Nat) w) pal)
      (erased (PalLength (Nat) w width) len) -> (ManSpan xs)))
  ((ManSeed : ((List (Nat)) left right) -> Type) enum
    (many MkManSeed : (erased (List (Nat)) left right common)
      (many (List (Nat)) lrest rrest) (many (Nat) k)
      (erased (PalConcat (Nat) common lrest left) cl)
      (erased (PalConcat (Nat) common rrest right) cr)
      (erased (PalLength (Nat) common k) len) -> (ManSeed left right))))

(def-fns _ $ (many man-index : (erased (List (Nat)) xs)
    (many (List (Nat)) left) (subterm many (List (Nat)) right)
    (many (Nat) i) (erased (PalCut xs i left right) p)
    (many (IdMap (ManCut xs)) table) -> (many (IdMap (ManCut xs)) out))
  (let ((many next)) (idmap-set _ i (MkManCut _ i left right p) table))
  (let-match many right (Cons _ x rest) ((Nil _) next))
  (tail (man-index xs (Cons _ x left) rest (Succ i)
    (fp-cut-step xs left rest i x p) next)))

(def-fns _ $ (many man-cut : (erased (List (Nat)) xs)
    (many (IdMap (ManCut xs)) table) (many (Nat) i) ->
    (many (Maybe (ManCutAt xs i)) out))
  (let-match many (idmap-get _ i table) (Hit _ _ _ entry _) ((Miss _ _ _ _) (None _)))
  (let-match many entry (MkManCut _ j left right cut))
  (match many (nat-cmp i j) _
    ((CEq _ _ _) (Some _ (MkManCutAt _ _ left right cut)))
    (else (None _))))

; Expansion is the only place input elements are compared. Its result is
; an exact LCP, including the mismatch or boundary that stops expansion.
(def-fns _ $ (many man-expand-acc : (erased (List (Nat)) fullleft fullright)
    (subterm many (List (Nat)) left) (many (List (Nat)) right) (many (Nat) n)
    (erased (PalLcpPrefix fullleft fullright left right n) prefix) ->
    (many (Nat) k) (erased (PalLcp fullleft fullright k) p))
  (let-match many left (Cons _ x l)
    ((Nil _) (values n (fp-lcp-prefix-close fullleft fullright left right n (Zero) n
      prefix (PLLeft right) (add-zero-right n)))))
  (let-match many right (Cons _ y r)
    ((Nil _) (values n (fp-lcp-prefix-close fullleft fullright left right n (Zero) n
      prefix (PLRight left) (add-zero-right n)))))
  (match many (nat-cmp x y) _
    ((CLt _ _ _ _ lt) (values n
      (fp-lcp-prefix-close fullleft fullright left right n (Zero) n prefix
        (PLApart x y l r (ApartLt _ _ lt)) (add-zero-right n))))
    ((CGt _ _ _ _ gt) (values n
      (fp-lcp-prefix-close fullleft fullright left right n (Zero) n prefix
        (PLApart x y l r (ApartGt _ _ gt)) (add-zero-right n))))
    ((CEq _ _ _)
      (tail (man-expand-acc fullleft fullright l r (Succ n)
        (PLPStep fullleft fullright l r x n prefix))))))

(def-fns _ $ (many man-expand : (many (List (Nat)) left right) ->
    (many (Nat) k) (erased (PalLcp left right k) p))
  (tail (man-expand-acc left right left right (Zero) (PLPStart left right))))

; Trim the cached mirror to the radius that fits inside the rightmost span.
; Numeric guards expose arithmetic equalities to the checker in O(1).
(def-fns _ $ (many man-trim : (erased (List (Nat)) xs)
    (many (ManSpan xs) span) (many (Nat) k width) ->
    (many (Maybe (ManSpan xs)) out))
  (let-match many span (MkManSpan _ w lo hi old oldwidth range pal len))
  (let-match many (lt-dec k (Succ old)) (Yes _ _ _ _ bound) ((No _ _ _ _ _) (None _)))
  (let ((many cut) (erased _)) (sub old k bound))
  (let ((many dc) (erased twice)) (double cut))
  (let ((many whole) (erased sum)) (add dc width))
  (let-match many (nat-cmp whole oldwidth) (CEq _ _ _) (else (None _)))
  (let ((many newlo) (erased al)) (add lo cut))
  (let ((many newhi) (erased size)) (add newlo width))
  (let ((erased before) (erased middle) (erased after) (erased rest)
       (erased cb) (erased ca) (erased lb) (erased _) (erased lm) (erased pm))
    (fp-pal-trim w cut dc width oldwidth pal len twice sum))
  (Some _ (MkManSpan _ _ newlo newhi k width
    (fp-trim-range xs w before middle after rest lo hi cut newlo newhi width
      range cb ca lb lm al size) pm lm)))

(def-fns _ $ (many man-reflect : (erased (List (Nat)) xs)
    (many (ManSpan xs) outer inner) -> (many (Maybe (ManSpan xs)) out))
  (let-match many outer (MkManSpan _ big l r _ _ outerRange bigpal _))
  (let-match many inner (MkManSpan _ w a b k width innerRange pal len))
  (let-match many (lt-dec l (Succ a)) (Yes _ _ _ _ lower) ((No _ _ _ _ _) (None _)))
  (let-match many (lt-dec b (Succ r)) (Yes _ _ _ _ upper) ((No _ _ _ _ _) (None _)))
  (let ((many after) (erased ar)) (sub r b upper))
  (let ((many lo) (erased al)) (add l after))
  (let ((many hi) (erased ah)) (add lo width))
  (Some _ (MkManSpan _ _ lo hi k width
    (fp-range-reflect xs big w l r a b lo hi after width outerRange innerRange
      bigpal pal lower upper ar al len ah) pal len)))

; Reify only the two endpoints of the proven mirror seed. Shared cut lists
; let expansion skip the entire known prefix with two trie lookups.
(def-fns _ $ (many man-seed-span : (erased (List (Nat)) xs)
    (erased (List (Nat)) left fullright right) (erased (List (Nat)) mid)
    (many (Nat) i extra) (erased (PalParity extra) parity)
    (erased (PalSplit xs left fullright) split) (erased (PalLength (Nat) left i) llen)
    (erased (PalLength (Nat) mid extra) mlen) (erased (PalConcat (Nat) mid right fullright) mcat)
    (many (IdMap (ManCut xs)) table) (many (ManSpan xs) span) ->
    (many (Maybe (ManSeed left right)) out))
  (let-match many span (MkManSpan _ w lo hi k width range pal len))
  (let ((many d) (erased twice)) (double k))
  (let ((many checkwidth) (erased count)) (add d extra))
  (let-match many (nat-cmp checkwidth width) (CEq _ _ _) (else (None _)))
  (let ((many checki) (erased offset)) (add lo k))
  (let-match many (nat-cmp checki i) (CEq _ _ _) (else (None _)))
  (let-match many (man-cut xs table lo) (Some _ lc) ((None _) (None _)))
  (let-match many lc (MkManCutAt _ _ ll lr low))
  (let-match many (man-cut xs table hi) (Some _ hc) ((None _) (None _)))
  (let-match many hc (MkManCutAt _ _ hl hr high))
  (let ((erased _) (erased lrest) (erased rrest)
       (erased cl) (erased cr) (erased lk)
       (erased loRight) (erased hiLeft) (erased lowcut) (erased highcut))
    (fp-center-seed xs left fullright right mid w i lo hi k d extra width
      split llen mlen mcat range pal len twice count parity offset))
  (let ((erased el) (erased _))
    (fp-cut-unique xs lrest loRight ll lr lo lowcut low))
  (let ((erased _) (erased er))
    (fp-cut-unique xs hiLeft rrest hl hr hi highcut high))
  (let-match erased el (Refl _ _))
  (let-match erased er (Refl _ _))
  (Some _ (MkManSeed _ _ _ ll hr k cl cr lk)))

(def-fns _ $ (many man-reuse : (erased (List (Nat)) xs)
    (erased (List (Nat)) left fullright right) (erased (List (Nat)) mid)
    (many (Nat) i extra) (erased (PalParity extra) parity)
    (erased (PalSplit xs left fullright) split) (erased (PalLength (Nat) left i) llen)
    (erased (PalLength (Nat) mid extra) mlen) (erased (PalConcat (Nat) mid right fullright) mcat)
    (many (IdMap (ManCut xs)) table) (many (IdMap (ManSpan xs)) radii)
    (many (Maybe (ManSpan xs)) frame) -> (many (Maybe (ManSeed left right)) out))
  (let-match many frame (Some _ outer) ((None _) (None _)))
  (let-match many outer (MkManSpan _ _ l r _ _ _ _ _))
  (let ((many edge)) (nat-add i extra))
  (let-match many (nat-cmp edge r) (CLt _ _ _ _ _) (else (None _)))
  (let ((many mirror)) (nat-sub (nat-add l r) edge))
  (let-match many (idmap-get _ mirror radii) (Hit _ _ _ inner _) ((Miss _ _ _ _) (None _)))
  (let-match many inner (MkManSpan _ _ _ _ mk _ _ _ _))
  (let ((many room)) (nat-sub r edge))
  (let ((many seed))
    (match many (nat-cmp mk room) (((Nat) k))
      ((CGt _ _ _ _ _) room) (else mk)))
  (let ((many width)) (nat-add (nat-add seed seed) extra))
  (let-match many (man-trim xs inner seed width) (Some _ trimmed) ((None _) (None _)))
  (let-match many (man-reflect xs outer trimmed) (Some _ reflected) ((None _) (None _)))
  (man-seed-span xs left fullright right mid i extra parity split llen
    mlen mcat table reflected))

(def-fns _ $ (many man-center : (erased (List (Nat)) xs)
    (many (List (Nat)) left) (erased (List (Nat)) fullright) (many (List (Nat)) right) (erased (List (Nat)) mid)
    (many (Nat) i extra) (erased (PalParity extra) parity)
    (erased (PalSplit xs left fullright) split) (erased (PalLength (Nat) left i) llen)
    (erased (Palindrome (Nat) mid) mp) (erased (PalLength (Nat) mid extra) mlen)
    (erased (PalConcat (Nat) mid right fullright) mcat)
    (many (IdMap (ManCut xs)) table) (many (IdMap (ManSpan xs)) radii)
    (many (Maybe (ManSpan xs)) frame) ->
    (many (Nat) k d width) (erased (PalLcp left right k) exact)
    (erased (Double k d) twice) (erased (Add d extra width) count)
    (many (ManSpan xs) span) (erased (HasPalindromeOfLength xs width) has))
  (let ((many k) (erased exact))
    (match many (man-reuse xs left fullright right mid i extra parity split llen mlen mcat
        table radii frame) (((Nat) k) ((PalLcp left right k) exact))
      ((None _) (man-expand left right))
      ((Some _ seed)
        (let-match many seed (MkManSeed _ _ common lrest rrest start cl cr len))
        (let ((many more) (erased tailproof)) (man-expand lrest rrest))
        (let ((many k) (erased sum)) (add start more))
        (values k (fp-lcp-prepend common lrest rrest left right start more k
          cl cr len tailproof sum)))))
  (let ((many d) (erased twice)) (double k))
  (let ((many width) (erased count)) (add d extra))
  (let ((many lo) (erased offset)) (sub i k (fp-lcp-bound left right k i exact llen)))
  (let ((many hi) (erased endpoint)) (add lo width))
  (let ((erased _) (erased range) (erased pal) (erased len))
    (fp-center-range xs left right k d exact twice mid fullright extra width
      split mp mlen mcat count i lo hi llen offset endpoint))
  (values k d width exact twice count (MkManSpan _ _ lo hi k width range pal len)
    (fp-center-witness xs left right k d exact twice mid fullright extra width
      split mp mlen mcat count)))

(def-fns _ $ (many man-frame : (erased (List (Nat)) xs)
    (many (Maybe (ManSpan xs)) old) (many (ManSpan xs) current) ->
    (many (Maybe (ManSpan xs)) out))
  (let-match many current (MkManSpan _ _ _ hi _ _ _ _ _))
  (let-match many old (Some _ previous) ((None _) (Some _ current)))
  (let-match many previous (MkManSpan _ _ _ hi2 _ _ _ _ _))
  (match many (nat-cmp hi2 hi) _
    ((CLt _ _ _ _ _) (Some _ current))
    (else old)))

(def-fns _ $ (many man-best : (erased (List (Nat)) xs) (many (Nat) a b)
    (erased (HasPalindromeOfLength xs a) ha) (erased (HasPalindromeOfLength xs b) hb) ->
    (many (Nat) n) (erased (HasPalindromeOfLength xs n) has)
    (erased (Lt a (Succ n)) ba) (erased (Lt b (Succ n)) bb))
  (match many (nat-cmp a b) _
    ((CLt _ _ _ _ p) (values b hb (lt-weaken a b p) (lt-succ b)))
    ((CEq _ _ _) (values a ha (lt-succ a) (lt-succ a)))
    ((CGt _ _ _ _ p) (values a ha (lt-succ a) (lt-weaken b a p)))))

; Two independent rightmost spans handle even and odd centers. The erased
; numeric maximum and erased history advance together, keeping the scan
; tail recursive while certifying all centers through fp-centers-spec.
(def-fns _ $ (many man-scan : (erased (List (Nat)) xs)
    (many (List (Nat)) left) (subterm many (List (Nat)) right) (many (Nat) i)
    (erased (PalSplit xs left right) split) (erased (PalLength (Nat) left i) llen)
    (many (IdMap (ManCut xs)) table)
    (many (IdMap (ManSpan xs)) evens odds)
    (many (Maybe (ManSpan xs)) evenframe oddframe)
    (many (Nat) best) (erased (HasPalindromeOfLength xs best) besthas)
    (erased (PalScanned xs left right best) scanned) ->
    (many (Nat) n) (erased (HasPalindromeOfLength xs n) has)
    (erased (PalCenterBounds (Nil (Nat)) xs n) bounds))
  (let-match many right (Cons _ x rest)
    ((Nil _)
      (values best besthas
        (fp-scanned-close xs left right best scanned (PCBEnd left best)))))
  (let ((erased e) (many de) (erased ew) (erased ep) (erased ed) (erased ec)
       (many es) (erased eh))
    (man-center xs left right right (Nil _) i (Zero) (PPEven) split llen
      (PalNil _) (PalLNil _) (PalCatNil _ right) table evens evenframe))
  (let-match erased (fp-add-unique de (Zero) ew de ec (add-zero-right de)) (Refl _ _))
  (let ((erased o) (many do) (erased ow) (erased op) (erased od) (erased oc)
       (many os) (erased oh))
    (man-center xs left right rest _ i (Succ (Zero))
      (PPOdd) split llen (PalOne _ x)
      (PalLCons _ x _ _ (PalLNil _))
      (PalCatCons _ x _ _ _ (PalCatNil _ rest)) table odds oddframe))
  (let-match erased (fp-add-unique do (Succ (Zero)) ow _ oc
    (add-succ-right do (Zero) do (add-zero-right do))) (Refl _ _))
  (let ((many here) (erased herehas) (erased be) (erased bo))
    (man-best xs de (Succ do) eh oh))
  (let ((many n) (erased has) (erased bh) (erased bb))
    (man-best xs here best herehas besthas))
  (tail (man-scan xs (Cons _ x left) rest (Succ i)
    (PSStep xs left rest x split) (PalLCons _ x _ _ llen) table
    (idmap-set _ i es evens) (idmap-set _ i os odds)
    (man-frame xs evenframe es) (man-frame xs oddframe os) n has
    (PSCStep xs left rest x n e o de do ep op ed od
      (fp-le-trans de here n be bh) (fp-le-trans _ here n bo bh)
      (fp-scanned-weaken xs left right best n scanned bb)))))

(def-fns _ $ (many longest-palindrome-manacher : (many (List (Nat)) xs) ->
    (many (Nat) n) (erased (LongestPalindrome xs n) correct))
  (let ((many table))
    (man-index xs (Nil _) xs (Zero)
      (MkPalCut xs (Nil _) (Nil _) xs (Zero)
        (PalCatNil _ xs) (RevNil _) (PalLNil _)) (MEmpty _)))
  (let ((many n) (erased has) (erased bounds))
    (man-scan xs (Nil _) xs (Zero) (PSStart xs) (PalLNil _) table
      (MEmpty _) (MEmpty _) (None _) (None _) (Zero)
      (HasHere _ (Zero) _ (TakeZero _ xs) (PalNil _))
      (PSCStart xs (Zero))))
  (values n (fp-centers-spec xs n bounds has)))
