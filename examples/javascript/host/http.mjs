export async function get(url) {
    const response = await fetch(url);
    if (!response.ok) throw new Error(`HTTP ${response.status}`);
    return response.text();
}

export async function apply(callback) {
    return (await callback(2n)) + (await callback(3n));
}
