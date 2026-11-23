// The JavaScript binding of the `HashMap` block of `std/hashmap.taut`. The map
// is a JavaScript `Map` from a key's hash (worked out in Tauto, under the map's
// seed) to a bucket of `[key, value]` entries, told apart by the `Key::eq` the
// call passes. Borrowed maps arrive as `{get, set}` views of this object.
const construct = (tag, names, fields, isStruct, owner) => ({ tag, names, fields, struct: isStruct, owner });
const some = (x) => construct('Some', null, [x], false, 'Option');
const none = () => construct('None', null, [], false, 'Option');
const pair = (a, b) => construct('Pair', ['fst', 'snd'], [a, b], true, 'Pair');
const view = (b, i) => ({ ref: true, get: () => b[i][1], set: (v) => { b[i][1] = v; } });
const key = (k) => { while (k && k.ref) k = k.get(); return k; };
const map = (m) => { while (m && m.ref) m = m.get(); return m; };

function find(s, h, k, eq) {
  const b = s.buckets.get(h);
  if (b === undefined) return [undefined, -1];
  for (let i = 0; i < b.length; i++) if (eq(b[i][0], k)) return [b, i];
  return [b, -1];
}

export function release(_m) {}
export function with_seed(seed) {
  return { seed, buckets: new Map(), size: 0 };
}
export function seed(m) {
  return map(m).seed;
}
export function len(m) {
  return BigInt(map(m).size);
}
export function get_at(m, h, k, eq) {
  const [b, i] = find(map(m), h, key(k), eq);
  return i < 0 ? none() : some(view(b, i));
}
export function get_mut_at(m, h, k, eq) {
  return get_at(m, h, k, eq);
}
export function contains_at(m, h, k, eq) {
  return find(map(m), h, key(k), eq)[1] >= 0;
}
export function remove_at(m, h, k, eq) {
  const s = map(m);
  const [b, i] = find(s, h, key(k), eq);
  if (i < 0) return none();
  const [e] = b.splice(i, 1);
  if (b.length === 0) s.buckets.delete(h);
  s.size--;
  return some(pair(e[0], e[1]));
}
function put(s, h, k, v) {
  const b = s.buckets.get(h);
  if (b === undefined) s.buckets.set(h, [[k, v]]);
  else b.push([k, v]);
  s.size++;
}
export function insert_at(m, h, k, v, eq) {
  const s = map(m);
  const [b, i] = find(s, h, k, eq);
  if (i < 0) {
    put(s, h, k, v);
    return pair(none(), none());
  }
  const old = b[i];
  b[i] = [k, v];
  return pair(some(pair(old[0], old[1])), none());
}
export function insert_with_at(m, h, k, f, eq) {
  const s = map(m);
  if (find(s, h, k, eq)[1] >= 0) return none();
  put(s, h, k, f());
  return none();
}
export function each_mut(m, f) {
  for (const b of map(m).buckets.values())
    for (let i = 0; i < b.length; i++) f(b[i][0], view(b, i));
  return null;
}
export function fold(m, init, f) {
  let acc = init;
  for (const b of map(m).buckets.values()) for (const e of b) acc = f(acc, e[0], e[1]);
  return acc;
}
export function into_vec(m) {
  const items = [];
  for (const b of map(m).buckets.values()) for (const e of b) items.push(pair(e[0], e[1]));
  return { kind: 'Vec', items };
}
