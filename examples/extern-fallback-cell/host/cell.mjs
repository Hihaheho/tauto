// Host Cell is a mutable box `{ n }`, not the Tauto struct layout
// `{ tag, names, fields, struct, owner }` with a `value` field.
export function newCell(value) {
  return { n: value };
}
export function getCell(cell) {
  return cell.n;
}
export function setCell(cell, value) {
  cell.n = value;
  return null;
}
export function releaseCell(_cell) {}
