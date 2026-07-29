/**
 * Live GPS hole + green map drawn to match the yardage book renderer:
 * modern course colors, brown topo contours, cyan→red green slope heatmap,
 * downhill break arrows, fringe ring, black green outline.
 */
(function (global) {
  const COLORS = {
    fairway: '#6F9E4E',
    teeBox:  '#8FBC6B',
    green:   '#8FBF72',
    rough:   '#4F7A38',
    trees:   '#1A3A16',
    water:   '#3E8A9E',
    sand:    '#E2C98A',
    text:    '#1A1A1A',
    topo:    '#8A6A45',
  };

  const YD_PER_M = 1.09361;
  const M_PER_DEG_LAT = 111320;

  function jetElevColor(t) {
    if (t < 0.25) {
      const u = t / 0.25;
      return [Math.round(30 * u), Math.round(180 + 40 * u), Math.round(255 - 40 * u)];
    }
    if (t < 0.5) {
      const u = (t - 0.25) / 0.25;
      return [Math.round(30 + 50 * u), Math.round(220 - 20 * u), Math.round(215 - 150 * u)];
    }
    if (t < 0.75) {
      const u = (t - 0.5) / 0.25;
      return [Math.round(80 + 140 * u), Math.round(200 + 40 * u), Math.round(65 - 40 * u)];
    }
    const u = (t - 0.75) / 0.25;
    return [Math.round(220 + 35 * u), Math.round(240 - 180 * u), Math.round(25 - 15 * u)];
  }

  function pointInPoly(x, y, poly) {
    let inside = false;
    for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
      const xi = poly[i][0], yi = poly[i][1];
      const xj = poly[j][0], yj = poly[j][1];
      const intersect = ((yi > y) !== (yj > y)) &&
        (x < ((xj - xi) * (y - yi)) / (yj - yi + 0.0) + xi);
      if (intersect) inside = !inside;
    }
    return inside;
  }

  function drawArrow(ctx, x1, y1, x2, y2) {
    const dx = x2 - x1, dy = y2 - y1;
    const len = Math.hypot(dx, dy) || 1;
    const ux = dx / len, uy = dy / len;
    const head = Math.max(9, len * 0.55);
    const halfW = head * 0.5;
    const shaftEndX = x2 - ux * head * 0.6;
    const shaftEndY = y2 - uy * head * 0.6;
    ctx.beginPath();
    ctx.moveTo(x1, y1);
    ctx.lineTo(shaftEndX, shaftEndY);
    ctx.stroke();
    ctx.beginPath();
    ctx.moveTo(x2, y2);
    ctx.lineTo(x2 - ux * head - uy * halfW, y2 - uy * head + ux * halfW);
    ctx.lineTo(x2 - ux * head + uy * halfW, y2 - uy * head - ux * halfW);
    ctx.closePath();
    ctx.fill();
  }

  function smoothClosed(points, iterations = 2) {
    if (!points || points.length < 4) return points || [];
    let pts = points.map(p => [p.lat, p.lon]);
    const a = pts[0], b = pts[pts.length - 1];
    if (Math.abs(a[0] - b[0]) < 1e-9 && Math.abs(a[1] - b[1]) < 1e-9) pts = pts.slice(0, -1);
    for (let n = 0; n < iterations; n++) {
      const next = [];
      const len = pts.length;
      for (let i = 0; i < len; i++) {
        const p0 = pts[i], p1 = pts[(i + 1) % len];
        next.push([0.75 * p0[0] + 0.25 * p1[0], 0.75 * p0[1] + 0.25 * p1[1]]);
        next.push([0.25 * p0[0] + 0.75 * p1[0], 0.25 * p0[1] + 0.75 * p1[1]]);
      }
      pts = next;
    }
    return pts.map(([lat, lon]) => ({ lat, lon }));
  }

  function asRings(v) {
    if (!v) return [];
    if (Array.isArray(v) && v.length && v[0] && typeof v[0].lat === 'number') return [v];
    return v.filter(Boolean);
  }

  function sampleElev(elev, lat, lon) {
    if (!elev?.g) return null;
    const { g, w, h, latmin, latmax, lonmin, lonmax } = elev;
    const vv = Math.max(0, Math.min(1, (lat - latmin) / (latmax - latmin)));
    const uu = Math.max(0, Math.min(1, (lon - lonmin) / (lonmax - lonmin)));
    const rf = vv * (h - 1), cf = uu * (w - 1);
    const r0 = Math.floor(rf), c0 = Math.floor(cf);
    const r1 = Math.min(h - 1, r0 + 1), c1 = Math.min(w - 1, c0 + 1);
    const tr = rf - r0, tc = cf - c0;
    const get = (r, c) => g[r * w + c];
    return get(r0, c0) * (1 - tr) * (1 - tc) + get(r0, c1) * (1 - tr) * tc +
      get(r1, c0) * tr * (1 - tc) + get(r1, c1) * tr * tc;
  }

  /** Marching-squares contours in lat/lon from course elev (yardage-book topo). */
  function buildTopoContours(elev, bbox, intervalM = 2) {
    if (!elev?.g) return [];
    const gw = 48, gh = 48;
    const grid = new Float32Array(gw * gh);
    let emin = Infinity, emax = -Infinity;
    for (let r = 0; r < gh; r++) {
      for (let c = 0; c < gw; c++) {
        const lat = bbox.latmin + (r / (gh - 1)) * (bbox.latmax - bbox.latmin);
        const lon = bbox.lonmin + (c / (gw - 1)) * (bbox.lonmax - bbox.lonmin);
        const e = sampleElev(elev, lat, lon);
        grid[r * gw + c] = e ?? 0;
        if (e != null) { if (e < emin) emin = e; if (e > emax) emax = e; }
      }
    }
    if (!Number.isFinite(emin) || emax - emin < 0.4) return [];
    const levels = [];
    const start = Math.ceil(emin / intervalM) * intervalM;
    for (let L = start; L < emax; L += intervalM) levels.push(L);

    const lines = [];
    const latAt = (r) => bbox.latmin + (r / (gh - 1)) * (bbox.latmax - bbox.latmin);
    const lonAt = (c) => bbox.lonmin + (c / (gw - 1)) * (bbox.lonmax - bbox.lonmin);
    const lerp = (a, b, t) => a + (b - a) * t;

    for (const L of levels) {
      for (let r = 0; r < gh - 1; r++) {
        for (let c = 0; c < gw - 1; c++) {
          const v00 = grid[r * gw + c], v10 = grid[r * gw + c + 1];
          const v01 = grid[(r + 1) * gw + c], v11 = grid[(r + 1) * gw + c + 1];
          const bits = (v00 >= L ? 1 : 0) | (v10 >= L ? 2 : 0) | (v11 >= L ? 4 : 0) | (v01 >= L ? 8 : 0);
          if (bits === 0 || bits === 15) continue;
          const edge = (e) => {
            if (e === 0) { // top
              const t = (L - v00) / ((v10 - v00) || 1e-9);
              return { lat: latAt(r), lon: lonAt(lerp(c, c + 1, t)) };
            }
            if (e === 1) { // right
              const t = (L - v10) / ((v11 - v10) || 1e-9);
              return { lat: latAt(lerp(r, r + 1, t)), lon: lonAt(c + 1) };
            }
            if (e === 2) { // bottom
              const t = (L - v01) / ((v11 - v01) || 1e-9);
              return { lat: latAt(r + 1), lon: lonAt(lerp(c, c + 1, t)) };
            }
            const t = (L - v00) / ((v01 - v00) || 1e-9);
            return { lat: latAt(lerp(r, r + 1, t)), lon: lonAt(c) };
          };
          // Cases that produce one segment
          const segs = {
            1: [0, 3], 2: [0, 1], 3: [3, 1], 4: [1, 2], 5: [0, 1, 3, 2], 6: [0, 2],
            7: [3, 2], 8: [3, 2], 9: [0, 2], 10: [0, 3, 1, 2], 11: [1, 2],
            12: [3, 1], 13: [0, 1], 14: [0, 3],
          }[bits];
          if (!segs) continue;
          for (let i = 0; i < segs.length; i += 2) {
            lines.push([edge(segs[i]), edge(segs[i + 1])]);
          }
        }
      }
    }
    return lines;
  }

  function makeProjector(hole, aim, cssW, cssH, padFrac, focusPts) {
    const mLon = M_PER_DEG_LAT * Math.cos(hole.tee.lat * Math.PI / 180);
    const mLat = M_PER_DEG_LAT;
    const ax = (aim.lon - hole.tee.lon) * mLon;
    const ay = (aim.lat - hole.tee.lat) * mLat;
    const alen = Math.hypot(ax, ay) || 1;
    const ux = ax / alen, uy = ay / alen;
    const toLocal = (p) => {
      const dx = (p.lon - hole.tee.lon) * mLon;
      const dy = (p.lat - hole.tee.lat) * mLat;
      return { x: dx * (-uy) + dy * ux, y: dx * ux + dy * uy };
    };

    let minX = Infinity, maxX = -Infinity, minY = Infinity, maxY = -Infinity;
    for (const p of focusPts) {
      const q = toLocal(p);
      if (q.x < minX) minX = q.x; if (q.x > maxX) maxX = q.x;
      if (q.y < minY) minY = q.y; if (q.y > maxY) maxY = q.y;
    }
    const pad = Math.max(12, (maxY - minY) * padFrac, (maxX - minX) * padFrac);
    minX -= pad; maxX += pad; minY -= pad; maxY += pad;
    const spanX = maxX - minX || 1;
    const spanY = maxY - minY || 1;
    const scale = Math.min(cssW / spanX, cssH / spanY) * 0.94;
    const ox = (cssW - spanX * scale) / 2;
    const oy = (cssH - spanY * scale) / 2;
    const proj = (p) => {
      const q = toLocal(p);
      return {
        x: ox + (q.x - minX) * scale,
        y: cssH - (oy + (q.y - minY) * scale),
      };
    };
    const unproj = (sx, sy) => {
      const qx = (sx - ox) / scale + minX;
      const qy = ((cssH - sy) - oy) / scale + minY;
      const dx = (-uy) * qx + ux * qy;
      const dy = ux * qx + uy * qy;
      return {
        lat: hole.tee.lat + dy / mLat,
        lon: hole.tee.lon + dx / mLon,
      };
    };
    const yardsToPx = (yd) => (yd / YD_PER_M) * scale;
    return { proj, unproj, toLocal, yardsToPx, scale };
  }

  function fillPolys(ctx, rings, proj, color) {
    ctx.fillStyle = color;
    for (const ring of rings) {
      if (!ring || ring.length < 3) continue;
      ctx.beginPath();
      ring.forEach((p, i) => {
        const s = proj(p);
        if (i === 0) ctx.moveTo(s.x, s.y); else ctx.lineTo(s.x, s.y);
      });
      ctx.closePath();
      ctx.fill();
    }
  }

  function strokePolys(ctx, rings, proj, color, lw) {
    ctx.strokeStyle = color;
    ctx.lineWidth = lw;
    ctx.lineJoin = 'round';
    for (const ring of rings) {
      if (!ring || ring.length < 2) continue;
      ctx.beginPath();
      ring.forEach((p, i) => {
        const s = proj(p);
        if (i === 0) ctx.moveTo(s.x, s.y); else ctx.lineTo(s.x, s.y);
      });
      ctx.closePath();
      ctx.stroke();
    }
  }

  function prepareCanvas(canvas, aspect) {
    const cssW = canvas.clientWidth || 360;
    const cssH = Math.round(cssW * aspect);
    const dpr = Math.min(2, window.devicePixelRatio || 1);
    canvas.width = Math.round(cssW * dpr);
    canvas.height = Math.round(cssH * dpr);
    canvas.style.height = cssH + 'px';
    const ctx = canvas.getContext('2d');
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    return { ctx, cssW, cssH };
  }

  function collectPts(hole, extras) {
    const pts = [hole.tee, hole.f, hole.m, hole.b];
    const push = (rings) => {
      for (const r of asRings(rings)) for (const p of r) pts.push(p);
    };
    push(hole.line);
    push(hole.green);
    push(hole.fw);
    push(hole.sand);
    push(hole.water);
    push(hole.woods);
    push(hole.tees);
    for (const p of extras || []) if (p) pts.push(p);
    return pts;
  }

  function drawOverlays(ctx, proj, yardsToPx, toLocal, overlays) {
    const {
      gpsPos, pin, land, landClub, brg, aimAt, expect,
    } = overlays;
    const aim = overlays.pin || overlays.flag || null;

    if (pin) {
      const s = proj(pin);
      ctx.strokeStyle = '#C62828';
      ctx.lineWidth = 2;
      ctx.beginPath();
      ctx.moveTo(s.x, s.y + 10);
      ctx.lineTo(s.x, s.y - 12);
      ctx.stroke();
      ctx.beginPath();
      ctx.moveTo(s.x, s.y - 12);
      ctx.lineTo(s.x + 10, s.y - 7);
      ctx.lineTo(s.x, s.y - 2);
      ctx.closePath();
      ctx.fillStyle = '#C62828';
      ctx.fill();
    }

    // Start-line aim (where to point the face) — dashed white
    if (gpsPos && aimAt) {
      const a = proj(gpsPos);
      const b = proj(aimAt);
      ctx.beginPath();
      ctx.moveTo(a.x, a.y);
      ctx.lineTo(b.x, b.y);
      ctx.strokeStyle = 'rgba(255,255,255,0.75)';
      ctx.lineWidth = 2;
      ctx.setLineDash([6, 5]);
      ctx.stroke();
      ctx.setLineDash([]);
      ctx.fillStyle = 'rgba(255,255,255,0.9)';
      ctx.beginPath();
      ctx.arc(b.x, b.y, 4, 0, Math.PI * 2);
      ctx.fill();
      ctx.font = '700 10px system-ui,sans-serif';
      ctx.fillText('AIM', b.x + 7, b.y - 6);
    }

    // Shot path ball → HIT HERE (solid yellow guide)
    if (gpsPos && land) {
      const a = proj(gpsPos);
      const b = proj(land);
      ctx.beginPath();
      ctx.moveTo(a.x, a.y);
      ctx.lineTo(b.x, b.y);
      ctx.strokeStyle = 'rgba(240, 193, 74, 0.85)';
      ctx.lineWidth = 2.5;
      ctx.setLineDash([10, 6]);
      ctx.stroke();
      ctx.setLineDash([]);
    }

    // HIT HERE — strategic landing target (yellow)
    if (land) {
      const s = proj(land);
      const stdev = landClub?.stdev;
      const spread = landClub?.spread;
      const alongPx = yardsToPx(Math.max(10, (stdev != null ? stdev * 1.8 : 12)));
      const acrossPx = yardsToPx(Math.max(8, ((spread != null ? spread : 14) / 2)));
      let shotAng = 0;
      if (gpsPos) {
        const a = toLocal(gpsPos);
        const b = toLocal(land);
        shotAng = Math.atan2(-(b.y - a.y), b.x - a.x);
      }
      ctx.save();
      ctx.translate(s.x, s.y);
      ctx.rotate(shotAng);
      ctx.beginPath();
      ctx.ellipse(0, 0, acrossPx, alongPx, 0, 0, Math.PI * 2);
      ctx.fillStyle = 'rgba(240, 193, 74, 0.45)';
      ctx.fill();
      ctx.strokeStyle = 'rgba(240, 193, 74, 1)';
      ctx.lineWidth = 3;
      ctx.stroke();
      // Inner bullseye
      ctx.beginPath();
      ctx.arc(0, 0, Math.max(6, Math.min(acrossPx, alongPx) * 0.32), 0, Math.PI * 2);
      ctx.fillStyle = 'rgba(240, 193, 74, 1)';
      ctx.fill();
      ctx.strokeStyle = '#1a1200';
      ctx.lineWidth = 1.5;
      ctx.stroke();
      ctx.restore();

      ctx.fillStyle = '#f0c14a';
      ctx.strokeStyle = 'rgba(0,0,0,0.55)';
      ctx.lineWidth = 3;
      ctx.font = '800 13px system-ui,sans-serif';
      ctx.strokeText('HIT HERE', s.x + 12, s.y - 12);
      ctx.fillText('HIT HERE', s.x + 12, s.y - 12);
      if (landClub?.id) {
        ctx.font = '700 12px system-ui,sans-serif';
        const lab = `${landClub.id} · ${Math.round(landClub.stock)} yd`;
        ctx.strokeText(lab, s.x + 12, s.y + 6);
        ctx.fillText(lab, s.x + 12, s.y + 6);
      }
    }

    if (pin) {
      const s = proj(pin);
      ctx.fillStyle = '#C62828';
      ctx.strokeStyle = 'rgba(0,0,0,0.45)';
      ctx.lineWidth = 3;
      ctx.font = '800 11px system-ui,sans-serif';
      ctx.strokeText('PIN', s.x + 10, s.y + 4);
      ctx.fillText('PIN', s.x + 10, s.y + 4);
    }

    // Expected finish if you aim the start line (subtle ring)
    if (expect && land && gpsPos) {
      const e = proj(expect);
      const w = proj(land);
      if (Math.hypot(e.x - w.x, e.y - w.y) > 8) {
        ctx.beginPath();
        ctx.arc(e.x, e.y, 5, 0, Math.PI * 2);
        ctx.strokeStyle = 'rgba(155, 229, 110, 0.9)';
        ctx.lineWidth = 2;
        ctx.stroke();
        ctx.fillStyle = 'rgba(155, 229, 110, 0.85)';
        ctx.font = '600 10px system-ui,sans-serif';
        ctx.fillText('EXPECT', e.x + 8, e.y + 3);
      }
    }

    if (gpsPos) {
      const s = proj(gpsPos);
      if (gpsPos.acc > 0) {
        const r = Math.max(6, Math.min(gpsPos.acc * (yardsToPx(YD_PER_M)), 36));
        ctx.beginPath();
        ctx.arc(s.x, s.y, r, 0, Math.PI * 2);
        ctx.fillStyle = 'rgba(94, 200, 255, 0.14)';
        ctx.fill();
      }
      ctx.beginPath();
      ctx.arc(s.x, s.y, 7, 0, Math.PI * 2);
      ctx.fillStyle = overlays.fromTee ? '#9BE56E' : '#5ec8ff';
      ctx.fill();
      ctx.strokeStyle = '#0c1512';
      ctx.lineWidth = 2;
      ctx.stroke();
      ctx.fillStyle = overlays.fromTee ? '#9BE56E' : '#5ec8ff';
      ctx.font = '700 11px system-ui,sans-serif';
      ctx.fillText(overlays.fromTee ? 'TEE' : 'YOU', s.x + 10, s.y + 4);
    }
  }

  /**
   * Yardage-book green inset: rough, woods, water, fairway, fringe, green base,
   * cyan→red slope heatmap, break arrows, sand, dark frame, Low/High legend.
   */
  function drawGreenInset(canvas, course, hole, overlays) {
    const { ctx, cssW, cssH } = prepareCanvas(canvas, 1.05);
    const green = smoothClosed(hole.green, 2);
    const aim = overlays.pin || hole.m;
    const showLand = overlays.land && overlays.landOnGreen !== false;
    const focusExtra = [
      overlays.gpsPos,
      showLand ? overlays.land : null,
      overlays.pin,
      showLand ? overlays.aimAt : null,
      showLand ? overlays.expect : null,
    ].filter(Boolean);
    const greenPts = green?.length ? green : [hole.m, hole.f, hole.b];
    // Zoom green view around HIT HERE only when landing on the green
    const cropPts = showLand && overlays.land
      ? greenPts.concat([overlays.land, overlays.aimAt, overlays.expect].filter(Boolean))
      : greenPts.concat(focusExtra.filter(p => p !== overlays.gpsPos || overlays.landOnGreen));
    const { proj, unproj, toLocal, yardsToPx } = makeProjector(
      hole, aim, cssW, cssH, 0.28, cropPts,
    );

    ctx.fillStyle = COLORS.rough;
    ctx.fillRect(0, 0, cssW, cssH);
    fillPolys(ctx, asRings(hole.woods), proj, COLORS.trees);
    fillPolys(ctx, asRings(hole.water), proj, COLORS.water);
    fillPolys(ctx, asRings(hole.fw), proj, COLORS.fairway);
    fillPolys(ctx, asRings(hole.tees), proj, COLORS.teeBox);

    if (green?.length >= 3) {
      // Fringe ring
      ctx.save();
      ctx.lineWidth = Math.max(6, yardsToPx(1.5));
      ctx.strokeStyle = COLORS.fairway;
      ctx.lineJoin = 'round';
      ctx.beginPath();
      green.forEach((p, i) => {
        const s = proj(p);
        if (i === 0) ctx.moveTo(s.x, s.y); else ctx.lineTo(s.x, s.y);
      });
      ctx.closePath();
      ctx.stroke();
      ctx.restore();

      fillPolys(ctx, [green], proj, COLORS.green);

      // Slope overlay — same jet + break arrows as renderer.js drawGreenSlopeOverlay
      const ge = hole.gElev;
      if (ge?.g?.length) {
        const greenPx = green.map(p => {
          const s = proj(p);
          return [s.x, s.y];
        });
        let bx0 = Infinity, by0 = Infinity, bx1 = -Infinity, by1 = -Infinity;
        for (const [x, y] of greenPx) {
          if (x < bx0) bx0 = x; if (y < by0) by0 = y;
          if (x > bx1) bx1 = x; if (y > by1) by1 = y;
        }
        const m = 4;
        bx0 = Math.max(0, Math.floor(bx0) - m);
        by0 = Math.max(0, Math.floor(by0) - m);
        bx1 = Math.min(cssW - 1, Math.ceil(bx1) + m);
        by1 = Math.min(cssH - 1, Math.ceil(by1) + m);

        const elevMap = new Float32Array(cssW * cssH);
        elevMap.fill(NaN);
        const vals = [];
        for (let iy = by0; iy <= by1; iy++) {
          for (let ix = bx0; ix <= bx1; ix++) {
            if (!pointInPoly(ix, iy, greenPx)) continue;
            const ll = unproj(ix, iy);
            const e = sampleElev(ge, ll.lat, ll.lon);
            if (e == null || !Number.isFinite(e)) continue;
            elevMap[iy * cssW + ix] = e;
            vals.push(e);
          }
        }

        if (vals.length >= 5) {
          vals.sort((a, b) => a - b);
          const lo = vals[Math.floor(vals.length * 0.02)];
          const hi = vals[Math.floor(vals.length * 0.98)];
          const range = Math.max(0.25, hi - lo);

          const layer = document.createElement('canvas');
          layer.width = cssW; layer.height = cssH;
          const lctx = layer.getContext('2d');
          const img = lctx.createImageData(cssW, cssH);
          const data = img.data;
          for (let iy = by0; iy <= by1; iy++) {
            for (let ix = bx0; ix <= bx1; ix++) {
              const e = elevMap[iy * cssW + ix];
              if (!Number.isFinite(e)) continue;
              const t = Math.max(0, Math.min(1, (e - lo) / range));
              const [r, g, b] = jetElevColor(t);
              const i = (iy * cssW + ix) * 4;
              data[i] = r; data[i + 1] = g; data[i + 2] = b; data[i + 3] = 255;
            }
          }
          lctx.putImageData(img, 0, 0);
          ctx.save();
          ctx.beginPath();
          greenPx.forEach(([x, y], i) => { if (i === 0) ctx.moveTo(x, y); else ctx.lineTo(x, y); });
          ctx.closePath();
          ctx.clip();
          ctx.drawImage(layer, 0, 0);
          ctx.restore();

          const yppG = 1 / Math.max(1e-6, yardsToPx(1));
          const step = Math.max(26, Math.round(2.0 / yppG));
          const off = Math.max(3, Math.round(0.9 / yppG));
          const metresPerPixel = yppG * 0.9144;
          const refGradient = 0.03 * metresPerPixel;
          const maxArrow = step * 0.78;
          const shaftW = Math.max(2.8, step / 6);
          const elevSafe = (x, y) => {
            const xi = Math.max(bx0, Math.min(bx1, Math.round(x)));
            const yi = Math.max(by0, Math.min(by1, Math.round(y)));
            return elevMap[yi * cssW + xi];
          };
          ctx.lineCap = 'round';
          ctx.lineJoin = 'round';
          for (let iy = by0 + step / 2; iy <= by1; iy += step) {
            for (let ix = bx0 + step / 2; ix <= bx1; ix += step) {
              const x = Math.round(ix), y = Math.round(iy);
              if (!pointInPoly(x, y, greenPx)) continue;
              const eR = elevSafe(x + off, y);
              const eL = elevSafe(x - off, y);
              const eD = elevSafe(x, y + off);
              const eU = elevSafe(x, y - off);
              if (![eR, eL, eD, eU].every(Number.isFinite)) continue;
              let gx = (eR - eL) / (2 * off);
              let gy = (eD - eU) / (2 * off);
              let mag = Math.hypot(gx, gy);
              if (mag < 1e-9) continue;
              const len = Math.max(step * 0.55, Math.min(mag / refGradient, 1) * maxArrow);
              const ndx = (-gx / mag) * len;
              const ndy = (-gy / mag) * len;
              const x1 = x - ndx / 2, y1 = y - ndy / 2;
              const x2 = x + ndx / 2, y2 = y + ndy / 2;
              if (!pointInPoly(x2, y2, greenPx) || !pointInPoly(x1, y1, greenPx)) continue;
              ctx.strokeStyle = 'rgba(255,255,255,0.75)';
              ctx.fillStyle = 'rgba(255,255,255,0.75)';
              ctx.lineWidth = shaftW + 2.5;
              drawArrow(ctx, x1, y1, x2, y2);
              ctx.strokeStyle = '#000000';
              ctx.fillStyle = '#000000';
              ctx.lineWidth = shaftW;
              drawArrow(ctx, x1, y1, x2, y2);
            }
          }
        }
      }

      strokePolys(ctx, [green], proj, '#1B5E20', Math.max(3, Math.round(cssW / 160)));
    }

    fillPolys(ctx, asRings(hole.sand), proj, COLORS.sand);

    // Low → High legend
    {
      const W = cssW, H = cssH;
      const barW = Math.max(90, Math.round(W * 0.28));
      const barH = Math.max(10, Math.round(H * 0.028));
      const pad = Math.max(10, Math.round(W * 0.025));
      const labelH = Math.max(12, Math.round(H * 0.032));
      const boxPad = Math.max(4, Math.round(pad * 0.4));
      const boxW = barW + boxPad * 2;
      const boxH = barH + labelH + boxPad * 2;
      const x0 = pad;
      const y0 = H - pad - boxH;
      ctx.fillStyle = 'rgba(255,255,255,0.88)';
      ctx.fillRect(x0, y0, boxW, boxH);
      ctx.strokeStyle = 'rgba(0,0,0,0.35)';
      ctx.lineWidth = 1;
      ctx.strokeRect(x0 + 0.5, y0 + 0.5, boxW - 1, boxH - 1);
      const bx = x0 + boxPad;
      const by = y0 + boxPad + labelH * 0.15;
      for (let i = 0; i < barW; i++) {
        const [r, g, b] = jetElevColor(i / (barW - 1));
        ctx.fillStyle = `rgb(${r},${g},${b})`;
        ctx.fillRect(bx + i, by + labelH * 0.7, 1, barH);
      }
      ctx.fillStyle = '#111';
      ctx.font = `600 ${Math.max(9, Math.round(labelH * 0.75))}px sans-serif`;
      ctx.textBaseline = 'top';
      ctx.textAlign = 'left';
      ctx.fillText('Low', bx, by);
      ctx.textAlign = 'right';
      ctx.fillText('High', bx + barW, by);
      ctx.textAlign = 'center';
      ctx.font = `500 ${Math.max(8, Math.round(labelH * 0.65))}px sans-serif`;
      ctx.fillStyle = '#333';
      ctx.fillText('Elevation', bx + barW / 2, by);
    }

    // Outer frame
    ctx.strokeStyle = '#1B5E20';
    ctx.lineWidth = Math.max(4, Math.round(cssW / 160));
    ctx.strokeRect(0, 0, cssW, cssH);

    drawOverlays(ctx, proj, yardsToPx, toLocal, overlays);
  }

  /**
   * Yardage-book hole view: rough → woods → water → fairway → tee → green →
   * brown topo contours → sand → black green outline.
   */
  function drawHoleView(canvas, course, hole, overlays) {
    const { ctx, cssW, cssH } = prepareCanvas(canvas, 1.35);
    const aim = overlays.pin || hole.m;
    const green = smoothClosed(hole.green, 2);
    const focus = collectPts(hole, [
      overlays.gpsPos, overlays.land, overlays.pin, overlays.aimAt, overlays.expect,
    ]);
    const { proj, toLocal, yardsToPx } = makeProjector(hole, aim, cssW, cssH, 0.08, focus);

    ctx.fillStyle = COLORS.rough;
    ctx.fillRect(0, 0, cssW, cssH);
    fillPolys(ctx, asRings(hole.woods), proj, COLORS.trees);
    fillPolys(ctx, asRings(hole.water), proj, COLORS.water);
    fillPolys(ctx, asRings(hole.fw), proj, COLORS.fairway);
    fillPolys(ctx, asRings(hole.tees), proj, COLORS.teeBox);
    if (green?.length) fillPolys(ctx, [green], proj, COLORS.green);

    // Topo contours (brown), under sand — like includeTopo in renderHole
    if (course.elev) {
      let minLat = Infinity, maxLat = -Infinity, minLon = Infinity, maxLon = -Infinity;
      for (const p of focus) {
        if (p.lat < minLat) minLat = p.lat; if (p.lat > maxLat) maxLat = p.lat;
        if (p.lon < minLon) minLon = p.lon; if (p.lon > maxLon) maxLon = p.lon;
      }
      const padLat = (maxLat - minLat) * 0.08 || 0.0004;
      const padLon = (maxLon - minLon) * 0.08 || 0.0004;
      const segs = buildTopoContours(course.elev, {
        latmin: minLat - padLat, latmax: maxLat + padLat,
        lonmin: minLon - padLon, lonmax: maxLon + padLon,
      }, 2.0);
      ctx.strokeStyle = COLORS.topo;
      ctx.globalAlpha = 0.55;
      ctx.lineWidth = Math.max(1, yardsToPx(0.8));
      for (const [a, b] of segs) {
        const pa = proj(a), pb = proj(b);
        ctx.beginPath();
        ctx.moveTo(pa.x, pa.y);
        ctx.lineTo(pb.x, pb.y);
        ctx.stroke();
      }
      ctx.globalAlpha = 1;
    }

    fillPolys(ctx, asRings(hole.sand), proj, COLORS.sand);
    if (green?.length) {
      strokePolys(ctx, [green], proj, '#000000', Math.max(2, yardsToPx(2.2)));
    }

    // F/M/B + tee labels (subtle)
    for (const [p, label] of [[hole.f, 'F'], [hole.m, 'M'], [hole.b, 'B']]) {
      const s = proj(p);
      ctx.fillStyle = 'rgba(0,0,0,0.55)';
      ctx.beginPath();
      ctx.arc(s.x, s.y, 3, 0, Math.PI * 2);
      ctx.fill();
      ctx.font = '600 10px system-ui,sans-serif';
      ctx.fillText(label, s.x + 5, s.y - 4);
    }
    {
      const s = proj(hole.tee);
      ctx.fillStyle = COLORS.teeBox;
      ctx.fillRect(s.x - 4, s.y - 4, 8, 8);
      ctx.strokeStyle = '#000';
      ctx.lineWidth = 1;
      ctx.strokeRect(s.x - 4, s.y - 4, 8, 8);
    }

    // Border like yardage book
    const borderW = Math.max(3, Math.round(cssW * 0.006));
    ctx.strokeStyle = '#1A1A1A';
    ctx.lineWidth = borderW;
    ctx.strokeRect(borderW / 2, borderW / 2, cssW - borderW, cssH - borderW);

    drawOverlays(ctx, proj, yardsToPx, toLocal, overlays);
  }

  function render(opts) {
    const { course, hole, holeCanvas, greenCanvas, panel, titleEl, legEl, greenLabelEl } = opts;
    if (!course || !hole) {
      if (panel) panel.hidden = true;
      return;
    }
    if (panel) panel.hidden = false;
    if (titleEl) titleEl.textContent = `Hole ${hole.n}${hole.par ? ` · Par ${hole.par}` : ''}`;
    if (legEl) {
      if (opts.plan) {
        const p = opts.plan;
        const where = p.mode === "green" ? "on the green (yellow)" : p.mode === "layup" ? "short of green (yellow on hole map)" : "in the fairway (yellow on hole map)";
        legEl.textContent = `${p.club.id} · ${Math.round(p.stock)} yd → ${where}`;
      } else if (opts.landClub) {
        legEl.textContent = `Land ${opts.landClub.id} · ${Math.round(opts.landClub.stock)} yd`;
      } else if (opts.fromTee) {
        legEl.textContent = 'From tee · pick club call below';
      } else if (opts.gpsPos) {
        legEl.textContent = 'Waiting for club call…';
      } else {
        legEl.textContent = 'Pick a hole to see where to hit it';
      }
    }
    if (greenLabelEl) {
      if (opts.plan?.mode === "green") {
        greenLabelEl.textContent = "Green · yellow = land it here (red = pin)";
      } else if (opts.plan) {
        greenLabelEl.textContent = "Green contour · landing is on the hole map above (yellow)";
      } else {
        greenLabelEl.textContent = "Green · yellow = land it here";
      }
    }

    const overlays = {
      gpsPos: opts.gpsPos || null,
      fromTee: !!opts.fromTee,
      pin: opts.pin || null,
      land: opts.land || null,
      landClub: opts.landClub || null,
      landOnGreen: opts.landOnGreen !== false,
      aimAt: opts.aimAt || null,
      expect: opts.expect || null,
      brg: opts.brg != null ? opts.brg : null,
      flag: opts.pin || hole.m,
    };
    if (holeCanvas) drawHoleView(holeCanvas, course, hole, overlays);
    // Always try to show HIT HERE on the green when the landing is on/near it;
    // for fairway/layup keep green as contour-only so the yellow stays on the hole map.
    if (greenCanvas) {
      const onGreen = opts.landOnGreen && opts.land;
      const greenOverlays = onGreen
        ? overlays
        : { ...overlays, land: null, landClub: null, aimAt: null, expect: null, landOnGreen: false, gpsPos: null };
      drawGreenInset(greenCanvas, course, hole, greenOverlays);
    }
  }

  global.YardageLiveMap = { render, COLORS };
})(typeof window !== 'undefined' ? window : globalThis);
