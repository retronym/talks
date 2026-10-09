"""Divergence families of the names space, by the edit and the model's resolution before and after."""

def family(edit, before, after):
    """The divergence family of an edit, by the slot it changes and whether resolution moved."""
    kind, *slots = edit.split()
    dest = slots[-1]
    if after == 'clash':
        return 'F5 missed clash'
    if kind in ('add', 'unrename', 'move') and dest in ('inner', 'outer', 'wpkg'):
        return 'F1 added class'
    if kind == 'add' and dest == 'pobj':
        return 'F2 package object member' if before != after else 'F4 stale mirror'
    if kind == 'add' and dest == 'wild':
        return 'F3 wildcard import, other class'
    return 'other ' + kind + ' ' + dest


def givens_family(edit, before, after):
    kind, *slots = edit.split()
    dest = slots[-1]
    if before == after or dest in ('inh', 'wild', 'blk', 'comp'):
        return 'G3 trait initialiser, compiled apart (Scala 3, bytes only)'
    if kind in ('add', 'move') and dest == 'pobj':
        return 'G1 package object instance'
    if kind in ('add', 'move') and dest in ('inner', 'outer'):
        return 'G2 top-level given (Scala 3) / package object a (Scala 2)'
    return 'other ' + kind + ' ' + dest
