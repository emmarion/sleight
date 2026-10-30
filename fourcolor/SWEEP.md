# Part A by a sweep: from a `Drawing` to a `PlaneMap`

Written by a Claude session working without the owner. This is the idea
behind part A's proof, which needs no Jordan curve theorem; the proof
itself is the code PLAN.md's Status lists, and where this sketch and the
code differ, the code is what the compilers checked. The section on one
chain of corner groups is the version the code follows.

## Idea

Order the points lexicographically, by x then y. Process them in that
order. At point v, add to the map every edge from v to an earlier point.
Write D_t for the drawing of the points processed so far and the edges
among them, and M_t for its map.

An edge is **active** at time t when its earlier endpoint has been
processed and its later one has not. Active edges are segments that
cross the vertical sweep line through the next point; they are not yet
in M_t. Two active edges never cross, so they are totally ordered from
bottom to top along the sweep line, and that order does not change while
both stay active. For an active edge a with processed endpoint u, its
**corner** c_a is the corner of M_t at u that contains the direction of
a; when u has no dart yet, c_a is a placeholder.

The invariant, for every component K of M_t that has active edges:

(I) the corners of K's active edges, taken in the sweep order, lie on
    one face orbit O_K of M_t, in its walk order, going round at most
    once (consecutive active edges may share a corner);

(L) no two components interleave in the sweep order as K1 K2 K1 K2.

## The step at v

1. The active edges ending at v are consecutive in the sweep order, say
   a_1 .. a_k from bottom to top, with earlier endpoints u_1 .. u_k
   (geometric fact: nothing lies between them near v without crossing
   one or passing through v).
2. Insert a_1 .. a_k in that order:
   - a_1: `PMIsolated` if u_1 has no dart, otherwise `PMPendant` at
     c_{a_1}.
   - a_i, i > 1: if u_i has no dart, `PMPendant` from v's corner after
     a_{i-1}. Otherwise join v's corner after a_{i-1} to c_{a_i}: if u_i
     is in the component of u_{i-1}, (I) shows both corners lie on
     O_K, which is `JoinFace`; if not, the components differ, which is
     `JoinApart`. v is a new vertex, so no loop arises.
3. Each join of corners on one orbit splits it in two. The piece
   between a_{i-1} and a_i holds no active corner, because a_{i-1} and
   a_i are consecutive. The other piece becomes the orbit of the merged
   component. A join of two components splices their orbits.
4. Edges from v to later points become active at v's place in the sweep
   order, sorted by slope, all at v's corner after a_k (or at a
   placeholder when k = 0).
5. (I) and (L) hold again. For (I), the walk segments between
   consecutive active corners tile the old orbit; an insertion changes
   the face permutation only at the corner it is inserted into, which is
   an endpoint of the segments, so every segment that is not cut
   survives unchanged. For (L), a merge of two components that are
   adjacent in the sweep order cannot create an interleaving, by a
   short case analysis on positions.

## Refinement: one chain of corner groups

Components can be avoided altogether. When a point v has no edge to an
earlier point, add a **virtual** edge from v to a corner next to v's
place in the sweep order. A virtual edge is an edge of the map but not
of the drawing; a colouring of the map is then proper on a supergraph,
which is still enough. Start with a virtual point v0 joined to the first
point. The map is then connected throughout, and the frontier is one
cyclic list of **groups**: a group is a corner (the corner after a dart
d) with the active edges whose corner it is, in sweep order. Groups may
be empty. The invariant:

- the darts of the groups are distinct;
- for each group and the next one, cyclically, a face walk from nd(d)
  to e(d') that passes no group's corner (`Walk` in `walk.sl`);
- each group's items are labelled with the point of its dart.

The step at v, with the list rotated so that the run of closed edges
starts in the head group (d, B ++ R):

- the first edge is a pendant at d: groups (d, B), (y1, []), (x1, R
  without its head), the rest; the two new links are empty walks and
  the third is the old link out of the head group;
- each further closed edge, at the corner c of the third group, is a
  chord from the corner after y1 to c: the link from the second group
  to the third, plus the corner step at c, is the `FaceReach` that
  `JoinFace` needs; the new third group is (x, ...), and the old link
  is dropped with the face it closes;
- an empty third group in the way is dropped by joining the walks on
  either side of it through its corner, which is no longer in the set
  of corners to avoid;
- finally v's new active edges go into the second group (y1, ...).

Inserting y(i+1) right after y1 gives v the rotation y1, y(i+1), y(i),
.., y2, which is the order that makes each wedge between two of v's
edges close into its own face.

## Reading the colouring back

Each point gets one representative dart. Every dart is labelled with its
point, the node permutation keeps the label, and the darts of a point
form one node cycle, so the colouring of `Colored` is constant on them;
the edge permutation joins the two endpoints of a drawn edge, so their
colours differ. `ColorOf` then reads each point's colour from a list of
`MkPaint`, one per point.

## What the geometry has to supply

Only facts about the bottom-to-top order of segments on a vertical
line, all from `Left` and `Compatible`:

- G1: two active edges that do not cross keep their order;
- G2: the edges ending at v are consecutive, and their order matches
  the order in which they are inserted around v;
- G3: the edges starting at v fit into v's gap, ordered by slope;
- vertical edges, and points sharing an x coordinate, handled by the
  lexicographic order.

No angle comparison around a point is needed: the rotation at each
vertex is whatever the insertions produce.

## What the combinatorics has to supply

Shared with part B: the edge and node lists stay permutations; the
effect of an `Insert` on the face permutation; a join on one orbit splits
it into two explicitly described orbits; a join of two orbits splices
them; a `FaceReach` path that does not pass the changed corner survives
an insertion.
