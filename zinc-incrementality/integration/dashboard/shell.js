// The dashboard runtime page.html calls (dash.calc, dash.data, dash.onData, dash.params, ...),
// reading the datasets from the local server and polling for new ones after each lockstep round.
(() => {
  const NAMES = ['campaign', 'cells', 'steps', 'phases', 'cycles', 'edits', 'branches'];
  const data = {};
  const calcs = {};
  const callbacks = [];
  let cache = {};
  const load = (k, d) => { try { return JSON.parse(localStorage.getItem(k)) ?? d; } catch (e) { return d; } };
  let params = load('dash-params', {});
  const fire = () => {
    cache = {};
    for (const f of callbacks) { try { f(); } catch (e) { console.error(e); } }
  };
  window.dash = {
    calc(id, spec) { calcs[id] = spec; },
    onData(cb) { callbacks.push(cb); },
    data(id) {
      if (data[id]) return data[id];
      const c = calcs[id];
      if (!c) return { status: 'loading', data: [] };
      if (!cache[id]) {
        const ins = c.inputs.map((i) => this.data(i));
        const bad = ins.find((x) => x.status !== 'ok');
        if (bad) return { status: bad.status, data: [] };
        try { cache[id] = { status: 'ok', data: c.fn(...ins.map((x) => x.data)) }; }
        catch (e) { console.error(e); cache[id] = { status: 'error', data: [] }; }
      }
      return cache[id];
    },
    params() { return params; },
    setParams(p) { params = { ...params, ...p }; try { localStorage.setItem('dash-params', JSON.stringify(params)); } catch (e) { /* none */ } fire(); },
    setLink(id) { history.replaceState(null, '', '#' + id); },
    colors: ['#8a8984', '#c4673f', '#2f8f6b', '#b8862b', '#a94f75', '#2c6e2e', '#6e63b5', '#b5524b'],
  };
  let version = null;
  async function refresh() {
    try {
      const v = await (await fetch('data/version', { cache: 'no-store' })).text();
      if (v === version) return;
      version = v;
      await Promise.all(NAMES.map(async (n) => {
        const r = await fetch(`data/${n}.json`, { cache: 'no-store' });
        data[n] = r.ok ? { status: 'ok', data: await r.json() } : { status: 'missing', data: [] };
      }));
      document.getElementById('shell-updated').textContent = 'data ' + new Date().toLocaleTimeString();
      fire();
    } catch (e) { console.error(e); }
  }
  addEventListener('DOMContentLoaded', () => { refresh(); setInterval(refresh, 3000); });
  let t;
  addEventListener('resize', () => { clearTimeout(t); t = setTimeout(fire, 150); });
})();
