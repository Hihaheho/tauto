# Mutable state model

The models in `meta/mutable_*.taut` describe state passing with returned
mutable places. They use ordinary kernel terms and no axioms. They do not
change the surface language or specify a compiler implementation.

## Representations

`mutable_state.taut` represents a total place by its observation and writeback
functions. `PlaceLaws` states read-after-write, write-back-of-read, and
last-write-wins. `field_laws` preserves these laws under composition.
`Separate` states noninterference and commuting writes. A result may contain
multiple places, while one state contains all borrowed roots. Whole and partial
results therefore share the same state instead of keeping independent copies.

`mutable_container.taut` represents a variable-length container by a list and
its owner metadata. An element reference records an owner, generation and
index. `ValidRef` requires a live owner, matching generation, an open region,
and an in-bounds index. Element replacement preserves the index domain;
distinct-index writes preserve each other's observations and commute.

`reshape` increments the generation on structural replacement. This is a
conservative invalidation policy: an in-bounds index alone does not establish
that the element retains its identity. Closing an owner or its region also
invalidates its references. `CellFrame` preserves reference validity; it does
not by itself authorize writes to a borrowed value.

## Operation-dependent answers

`mutable_effects.taut` uses `Comp` with a dependent answer family. State loads
and saves occupy one side of `OpSum`; external operations occupy the other.
Each external continuation accepts exactly its operation's answer type.
Answers may themselves contain reference descriptors.

`lower` removes the state instructions. Each remaining operation carries the
state at suspension, and its reply contains both the typed answer and the
state at resumption. This keeps preceding writes observable to an aborting
handler and prevents resumption from restoring an obsolete state snapshot.
The protocol is a semantic representation, not permission for a source
handler to inspect or mutate every borrowed object.

## Ownership and lifetime conditions

`mutable_permissions.taut` describes logical authority separately from
copyable proof-level descriptors.

- `Permissions` requires unique active loan tokens and compatible footprints.
  Overlapping loans are compatible only when both are shared. Paths include
  whole roots and nested fields or element indices.
- Reading a reference requires active authority. Writing also requires a
  mutable authority. Moving or destroying an owner requires it to be
  unborrowed. `OwnershipStep` distinguishes transfer from destruction and
  forbids dropping a linear value or transferring a value twice.
- A reborrow has a fresh token, derives from the parent's root and path, and
  cannot strengthen a shared authority to mutable. The parent is absent from
  the active list while the child is active. Restoration uses the same
  remaining capabilities after the child has been released.
- `Returnable` requires provenance in the admitted input or handler roots and
  validity in the caller. Scope exit cannot leave an active loan pointing into
  the closed region. Generation and region checks do not replace provenance.

`mutable_conditions.taut` packages a payload, active loans and live owned-value
kinds into `World`. `WorldValid` combines permissions and the payload-specific
validity of every active loan. Acquisition requires both a compatible fresh
loan and a validity proof. The payload validity predicate connects a logical
loan to its concrete descriptor, path, generation and lifetime.

## Resumption conditions

The liveness conditions follow `ownership.md`「CFL rules」.

| Live value | `0` | `<=1` | `1` | `ω` |
|---|---|---|---|---|
| Duplicable or shared borrow | allowed | allowed | allowed | allowed |
| Affine or mutable borrow | cleanup on abort | allowed | allowed | rejected |
| Linear | rejected | rejected | allowed | rejected |

`Suspension` derives borrowed-value liveness from the active loans as well as
checking the owned values. `can_suspend` also excludes borrowed operation
arguments. Mutable borrowed answers exclude `ω` even when no
mutable loan was live before the operation. `ArmSafe` additionally checks
captures and requires an in-place continuation when the handled computation
borrows outside its scope.

`Body` describes actual continuation calls and branches on their results.
`BodySafe` checks permission at each call and the final call count on every
path. `body_count_sound` relates this judgment to `actual_calls`; an asserted
count is not substituted for checking the body. A non-resuming handler must
also satisfy its cleanup and result obligations.

## Conditional preservation

`source_safe` requires all of the following:

- the state invariant at every source instruction and return;
- an authorized update contract at every save, including ownership transitions;
- the suspension condition at every external operation;
- the remaining computation's safety for every typed answer and state admitted
  by the handler transfer contract;
- the postcondition at normal return, including validity and provenance of any
  returned loans.

`lower_agrees` equates direct interpretation with folding the translated tree,
for handlers that respect pointwise equality of their continuations. No
function-extensionality axiom is used. `lowering_safe` preserves the safety
obligations in the translated tree.
`checked_lowering` instantiates the invariant and suspension conditions with
`WorldValid` and the ownership/resumption model. Internal update contracts are
source obligations; eliminating their instructions does not establish them.
`handled_safe` additionally requires the return and operation arms to preserve
the handler's result property, including on abort. Count safety and capture
safety are separate obligations on those arms.

The count, borrowed-argument and mutable-result metadata must match the
operation declarations and their actual types. Owned-value lists must describe
the actual live resources, and update contracts must account for changes to
those lists. These are sufficient conditions, not an automatic ownership checker. In
particular, arbitrary predicates supplied as update or transfer contracts do
not certify real executions. Their interpretation must authorize precisely the
source accesses, preserve frozen owners and reference identities, account for
moved and destroyed values, and validate borrowed answers and returned loans.

## Scope

The computation and handler trees are inductive. The model describes finite
sequential computations, not divergence or concurrent interleavings. Container
storage is semantic; allocation, physical relocation, and backend drop behavior
are not modeled. Paths assume a consistent mapping to concrete disjoint
storage. The models prove no correspondence between the surface reader, Nib,
or a backend and these representations.

The executable proof checks and rejected claims are in
`cases/check/mutable-state-model.eure`. The six call shapes and mixed roots are
in `mutable_state_examples.taut`; dependent answers, containers and checked
suspension are in `mutable_extended_examples.taut`.
