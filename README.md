# IterTree

Lean encoding of `iTree`s inspired by Lean's `Std.Iter` type.

The `Std.Iter` implementation keeps in its signature the type
of the internal state the iterator uses to make progress. The
`step` operation is then obtained from this internal state
using a typeclass which maps internal states to a particular 
`step` function. Then, the `Std.Iter` is actually just the
current value of the internal state which "implements" the
iterator.

In our `iTree` encoding we package together the type of the
internal state, the stepping function associated with this
type and the current internal state inside of a single
structure, to simplify reasoning over it. In the future, 
however, it'd be interesting to explore separating these
so they mimick the `Std.Iter` representation.

## Limitations

We would like to quotient the "state machine"-based encoding
we have by the `StrongBisim` relation to obtain a structure
which more closely corresponds with what an iTree actually
is. The only issue is that, in the quotient, one is not able
to define the `.vis` constructor computably without causing
an universe bump. One is able to dodge this universe bump if
they use a `noncomputable` version which makes use of
`Quotient.choice`, but while useful to reason about `iTree`s
it is not usable in regular computations.

<!--

Funnily enough, this means that we have two representations for
our interaction trees. One which is fully computable (`iTree`), 
and one which is noncomputable (`iTree'`). But there is a 
correspondance between one and the other.

-->

