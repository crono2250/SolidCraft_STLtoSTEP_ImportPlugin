"""Procedural stock with two separate holes on perpendicular axes.

The rectangular outer edges share exactly the same subdivision on both faces.
The two holes are cylinders with disjoint radius envelopes in the common
transverse coordinate. This file is a local fixture recipe, independent of any
user-provided mesh.
"""
from collections import Counter
from math import atan2, cos, sin, tau

SIDE = 20.
R = 1.25
BORES = {0: (6., 8.), 2: (13., 14.)}
CORNERS = [(0., 0.), (SIDE, 0.), (SIDE, SIDE), (0., SIDE)]

def xyz(axis, level, uv):
    row = [0., 0., 0.]
    row[axis] = level
    row[(axis + 1) % 3], row[(axis + 2) % 3] = uv
    return tuple(row)

def radial_inventory(c):
    theta = [atan2(y-c[1], x-c[0]) % tau for x, y in CORNERS]
    sample = sorted(set(theta + [tau * i / 64 for i in range(64)]))
    ring = [(c[0] + R*cos(a), c[1] + R*sin(a)) for a in sample]
    starts = [sample.index(a) for a in theta]
    groups = []
    for a, b in zip(starts, starts[1:] + starts[:1]):
        groups.append(ring[a:b+1] if a < b else ring[a:] + ring[:b+1])
    return ring, groups

def on_segment(a, b, p):
    axis = next(j for j in range(3) if a[j] != b[j])
    return all(a[j] == p[j] for j in range(3) if j != axis) and min(a[axis],b[axis]) <= p[axis] <= max(a[axis],b[axis])

def sorted_edge(a, b, inventory):
    axis = next(j for j in range(3) if a[j] != b[j])
    return sorted({a,b} | {p for p in inventory if on_segment(a,b,p)},
                  key=lambda p:p[axis], reverse=a[axis]>b[axis])

def geometry():
    extra = set()
    mids = {}
    for axis, (x, y) in BORES.items():
        mids[axis] = [(x, 0.), (SIDE, y), (x, SIDE), (0., y)]
        extra.update(xyz(axis, level, uv) for uv in mids[axis] for level in (0., SIDE))

    cells = []
    rings = {axis: radial_inventory(c) for axis, c in BORES.items()}
    for axis in range(3):
        for level in (0., SIDE):
            for i in range(4):
                a = xyz(axis, level, CORNERS[i])
                b = xyz(axis, level, CORNERS[(i+1)%4])
                outer = sorted_edge(a,b,extra)
                if axis not in BORES:
                    c = xyz(axis, level, (SIDE/2, SIDE/2))
                    patch = [(p,q,c) for p,q in zip(outer,outer[1:])]
                else:
                    m = xyz(axis, level, mids[axis][i])
                    inner = [xyz(axis,level,p) for p in rings[axis][1][i]]
                    j = outer.index(m)
                    patch = [(p,q,inner[0]) for p,q in zip(outer[:j],outer[1:j+1])]
                    patch += [(p,q,inner[-1]) for p,q in zip(outer[j:],outer[j+1:])]
                    patch += [(m,q,p) for p,q in zip(inner,inner[1:])]
                cells.extend(patch if level == SIDE else [(a,c,b) for a,b,c in patch])
    for axis, (ring, _) in rings.items():
        low = [xyz(axis,0.,uv) for uv in ring]
        high = [xyz(axis,SIDE,uv) for uv in ring]
        for i in range(len(ring)):
            j = (i+1)%len(ring)
            cells.extend([(low[i],high[i],high[j]),(low[i],high[j],low[j])])
    counts = Counter((a,b) for p,q,r in cells for a,b in [(p,q),(q,r),(r,p)])
    assert all(n == counts[(b,a)] == 1 for (a,b),n in counts.items())
    return cells
