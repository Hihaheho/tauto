# `--timings` of `tauto build` and `tauto check`. Statuses, backends, targets,
# phase names and cache states stay as they are.

timings-heading = build timings ({ $status }; { $backend } / { $target }; wall time):
timings-total = total
timings-generated-sources = generated sources: { $unchanged } unchanged, { $written } written (content equality)
timings-generated-unknown = generated source reuse: unknown
timings-native-cache = native cache: { $cache }
timings-proof-cache = proof cache: { $cache }
