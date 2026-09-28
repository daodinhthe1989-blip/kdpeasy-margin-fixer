/* ================================================================
   KDPEasy Margin Fixer — app.js
   Single classic script, IIFE-wrapped. No modules, no fetch, no CDN:
   everything must run by double-clicking index.html over file://.
   ================================================================ */
(function () {
  'use strict';

  /* ---- 1. CONSTANTS & PRESETS ---- */

  var DPI = 300;
  var BLEED_IN = 0.125;              // KDP bleed, per trimmed edge
  var MIN_MARGIN_NO_BLEED = 0.25;    // KDP minimum, no bleed
  var MIN_MARGIN_BLEED = 0.375;      // KDP minimum, with bleed
  var VARIANCE_THRESHOLD = 900;      // ~30 std-dev per channel
  var NEAR_WHITE_CUTOFF = 250;       // per channel
  var WORK_LONG_EDGE = 1000;         // border-analysis working copy cap
  var PREVIEW_LONG_EDGE = 1400;      // preview render cap
  var BIG_FILE_BYTES = 50 * 1024 * 1024;

  // All 16 official KDP paperback trim sizes, in KDP's own order/groups.
  var TRIM_SIZES = [
    { w: 5,    h: 8,     group: 'Standard' },
    { w: 5.06, h: 7.81,  group: 'Standard' },
    { w: 5.25, h: 8,     group: 'Standard' },
    { w: 5.5,  h: 8.5,   group: 'Standard' },
    { w: 6,    h: 9,     group: 'Standard' },
    { w: 6.14, h: 9.21,  group: 'Large' },
    { w: 6.69, h: 9.61,  group: 'Large' },
    { w: 7,    h: 10,    group: 'Large' },
    { w: 7.44, h: 9.69,  group: 'Large' },
    { w: 7.5,  h: 9.25,  group: 'Large' },
    { w: 8,    h: 10,    group: 'Large' },
    { w: 8.25, h: 6,     group: 'Large' },
    { w: 8.25, h: 8.25,  group: 'Large' },
    { w: 8.5,  h: 8.5,   group: 'Large' },
    { w: 8.5,  h: 11,    group: 'Large' },
    { w: 8.27, h: 11.69, group: 'Large', note: 'A4' }
  ];
  var DEFAULT_TRIM_INDEX = 14;       // 8.5 x 11

  var FILL_HINTS = {
    auto:  'Looks at the edge of your image and chooses White, Solid, or Blur.',
    white: 'Clean white border. Best for line art and coloring pages.',
    solid: "Fills with the average color from your image's edge.",
    blur:  'Stretches and blurs your image behind itself. Best for full-color art.'
  };

  // JPG is offered for long books: a busy AI page is ~7-11 MB as PNG but
  // ~1-2 MB as JPG, and KDP caps the manuscript file at 650 MB.
  var JPEG_QUALITY = 0.92;
  var FORMAT_HINTS = {
    png: 'Sharpest quality, best for line art. Files are larger.',
    jpg: 'Much smaller files (often 5–10× smaller), good for books with many pages. Print quality stays high.'
  };

  var BLEED_HINTS = {
    off: 'Your artwork sits inside the page with white space around it. This is what most coloring books use.',
    on:  'Your artwork runs off the edge of the page with no white border. Choose this only if your book is set up for bleed in KDP.'
  };

  var PLACEMENT_HINTS = {
    cover: 'Your artwork fills the page edge-to-edge, like real KDP bleed. A thin strip at the very outer edge may be trimmed off — the dashed line shows what stays safe.',
    fit:   'Your whole image is kept, with a small padded border around it. This won’t look like true bleed, but nothing is ever cropped.'
  };

  /* ---- 2. STATE ---- */

  var state = {
    source: null,          // upright, opaque canvas of the user's image
    fileName: '',
    fileSize: 0,
    trimIndex: DEFAULT_TRIM_INDEX,
    bleed: false,
    bleedPlacement: 'cover',  // 'cover' (true bleed, may crop the outer ring) | 'fit' (never crop)
    margin: MIN_MARGIN_NO_BLEED,
    marginMode: '0.25',    // dropdown value: a number string, or 'custom'
    marginTouched: false,  // has the user deliberately set a margin this session?
    fill: 'auto',
    format: 'png',           // 'png' | 'jpg' (download format)
    customSolidColor: null,  // hex string when the user picked their own, else null = auto-computed
    analysis: null,        // cached per loaded image; independent of trim/margin
    pyramid: null,         // cached half-size chain for stepped downscaling
    dividerPct: 50,
    guides: true,
    pendingBigFile: null,
    rendering: false
  };

  var el = {};             // cached DOM references, filled in section 10
  var previewRaf = 0;
  var marginDebounce = 0;
  var resizeDebounce = 0;
  var toastTimer = 0;

  /* -- small helpers -- */

  function $(id) { return document.getElementById(id); }

  function newCanvas(w, h) {
    var c = document.createElement('canvas');
    c.width = Math.max(1, Math.round(w));
    c.height = Math.max(1, Math.round(h));
    return c;
  }

  function smooth(ctx) {
    ctx.imageSmoothingEnabled = true;
    if ('imageSmoothingQuality' in ctx) ctx.imageSmoothingQuality = 'high';
  }

  // Fill-white-first (§6.2): every surface the image is drawn on starts white,
  // so transparent PNGs never carry alpha (or black) into analysis or export.
  function whiteCtx(canvas) {
    var ctx = canvas.getContext('2d');
    ctx.fillStyle = '#ffffff';
    ctx.fillRect(0, 0, canvas.width, canvas.height);
    smooth(ctx);
    return ctx;
  }

  // Inches, trailing zeros stripped: 8.5 -> "8.5", 11 -> "11", 5.06 -> "5.06"
  function fmtIn(n) { return String(parseFloat(n.toFixed(4))); }

  function trimLabelInches(t) { return fmtIn(t.w) + '" × ' + fmtIn(t.h) + '"'; }

  function bytesToMB(b) { return (b / (1024 * 1024)).toFixed(1); }

  // Small files read better in KB ("245 KB") than as "0.2 MB".
  function fmtFileSize(b) {
    return b < 1024 * 1024 ? Math.max(1, Math.round(b / 1024)) + ' KB' : bytesToMB(b) + ' MB';
  }

  function toHex(n) {
    var s = Math.max(0, Math.min(255, Math.round(n))).toString(16);
    return s.length === 1 ? '0' + s : s;
  }

  /* ---- 3. EXIF ORIENTATION ---- */

  // Minimal EXIF reader: finds tag 0x0112 (Orientation) in IFD0. Returns 1..8,
  // defaulting to 1 for PNGs, EXIF-less JPEGs and anything unparseable.
  function readOrientation(buf) {
    var view = new DataView(buf);
    var len = view.byteLength;
    if (len < 4 || view.getUint16(0, false) !== 0xFFD8) return 1;   // not a JPEG

    var offset = 2;
    while (offset + 4 <= len) {
      var marker = view.getUint16(offset, false);
      if ((marker & 0xFF00) !== 0xFF00) break;
      if (marker === 0xFFD8 || (marker >= 0xFFD0 && marker <= 0xFFD9)) { offset += 2; continue; }
      offset += 2;
      var size = view.getUint16(offset, false);
      if (marker === 0xFFE1) {
        if (offset + 10 > len) break;
        if (view.getUint32(offset + 2, false) !== 0x45786966) {      // "Exif"
          offset += size; continue;
        }
        var tiff = offset + 8;                                       // skip "Exif\0\0"
        if (tiff + 8 > len) return 1;
        var little = view.getUint16(tiff, false) === 0x4949;         // "II" / "MM"
        var dir = tiff + view.getUint32(tiff + 4, little);
        if (dir + 2 > len) return 1;
        var count = view.getUint16(dir, little);
        for (var i = 0; i < count; i++) {
          var entry = dir + 2 + i * 12;
          if (entry + 12 > len) break;
          if (view.getUint16(entry, little) === 0x0112) {
            var v = view.getUint16(entry + 8, little);
            return (v >= 1 && v <= 8) ? v : 1;
          }
        }
        return 1;
      }
      if (marker === 0xFFDA) break;                                  // start of scan
      offset += size;
    }
    return 1;
  }

  // Produces the upright source canvas. For 5-8 width/height are swapped.
  function applyOrientation(img, w, h, o) {
    var swap = (o >= 5 && o <= 8);
    var canvas = newCanvas(swap ? h : w, swap ? w : h);
    var ctx = whiteCtx(canvas);
    switch (o) {
      case 2: ctx.transform(-1, 0, 0, 1, w, 0); break;               // flip horizontal
      case 3: ctx.transform(-1, 0, 0, -1, w, h); break;              // rotate 180
      case 4: ctx.transform(1, 0, 0, -1, 0, h); break;               // flip vertical
      case 5: ctx.transform(0, 1, 1, 0, 0, 0); break;                // transpose
      case 6: ctx.transform(0, 1, -1, 0, h, 0); break;               // rotate 90 CW
      case 7: ctx.transform(0, -1, -1, 0, h, w); break;              // transverse
      case 8: ctx.transform(0, -1, 1, 0, 0, w); break;               // rotate 270 CW
      default: break;                                                // 1: none
    }
    ctx.drawImage(img, 0, 0, w, h);
    return canvas;
  }

  /* ---- 4. IMAGE LOADING ---- */

  function isSupportedType(file) {
    if (file.type === 'image/png' || file.type === 'image/jpeg') return true;
    return /\.(png|jpe?g)$/i.test(file.name || '');
  }

  function handleFiles(list) {
    if (!list || !list.length) return;
    var file = list[0];
    if (!isSupportedType(file)) {
      showBanner("That file type isn't supported. Please use a PNG or JPG image.");
      return;
    }
    if (file.size > BIG_FILE_BYTES) {
      state.pendingBigFile = file;
      showBanner('That image is very large (' + bytesToMB(file.size) +
                 ' MB) and may be slow to process. Continue anyway?', 'Continue', function () {
        var f = state.pendingBigFile;
        state.pendingBigFile = null;
        if (f) loadFile(f);
      });
      return;
    }
    loadFile(file);
  }

  function loadFile(file) {
    decodeUpright(file).then(function (canvas) {
      state.source = canvas;
      state.fileName = file.name || 'image.png';
      state.fileSize = file.size;
      state.analysis = null;                 // caches are per image
      state.pyramid = null;
      state.customSolidColor = null;         // a picked color was for the old image
      onImageReady();
    }).catch(function () {
      showBanner("We couldn't open that image. It may be damaged — try re-saving it and uploading again.");
    });
  }

  // A 2x1 JPEG carrying EXIF Orientation=6 (rotate 90 CW). A browser that
  // applies EXIF by itself reads it back as 1x2. We probe ONCE so that we
  //  - never rotate an image the browser has already rotated (double rotation), and
  //  - never trust an `imageOrientation` option an old Safari silently ignores.
  var PROBE_JPEG = '/9j/4AAQSkZJRgABAQAAAQABAAD/4QAiRXhpZgAATU0AKgAAAAgAAQESAAMAAAABAAYAAAAAAAD/2wBDAAMCAgMCAgMDAwMEAwMEBQgFBQQEBQoHBwYIDAoMDAsKCwsNDhIQDQ4RDgsLEBYQERMUFRUVDA8XGBYUGBIUFRT/2wBDAQMEBAUEBQkFBQkUDQsNFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBQUFBT/wAARCAABAAIDASIAAhEBAxEB/8QAHwAAAQUBAQEBAQEAAAAAAAAAAAECAwQFBgcICQoL/8QAtRAAAgEDAwIEAwUFBAQAAAF9AQIDAAQRBRIhMUEGE1FhByJxFDKBkaEII0KxwRVS0fAkM2JyggkKFhcYGRolJicoKSo0NTY3ODk6Q0RFRkdISUpTVFVWV1hZWmNkZWZnaGlqc3R1dnd4eXqDhIWGh4iJipKTlJWWl5iZmqKjpKWmp6ipqrKztLW2t7i5usLDxMXGx8jJytLT1NXW19jZ2uHi4+Tl5ufo6erx8vP09fb3+Pn6/8QAHwEAAwEBAQEBAQEBAQAAAAAAAAECAwQFBgcICQoL/8QAtREAAgECBAQDBAcFBAQAAQJ3AAECAxEEBSExBhJBUQdhcRMiMoEIFEKRobHBCSMzUvAVYnLRChYkNOEl8RcYGRomJygpKjU2Nzg5OkNERUZHSElKU1RVVldYWVpjZGVmZ2hpanN0dXZ3eHl6goOEhYaHiImKkpOUlZaXmJmaoqOkpaanqKmqsrO0tba3uLm6wsPExcbHyMnK0tPU1dbX2Nna4uPk5ebn6Onq8vP09fb3+Pn6/9oADAMBAAIRAxEAPwD50ooor8MP9Uz/2Q==';
  var orientProbe = null;

  function probeOrientationSupport() {
    if (orientProbe) return orientProbe;
    orientProbe = new Promise(function (resolve) {
      // Safe defaults if the probe cannot run: modern browsers auto-rotate <img>.
      var result = { imgAuto: true, bitmapOk: typeof createImageBitmap === 'function' };
      var settled = false;
      function finish() { if (!settled) { settled = true; resolve(result); } }
      setTimeout(finish, 1500);
      try {
        var bin = atob(PROBE_JPEG), bytes = new Uint8Array(bin.length);
        for (var i = 0; i < bin.length; i++) bytes[i] = bin.charCodeAt(i);
        var blob = new Blob([bytes], { type: 'image/jpeg' });
        var img = new Image();
        img.onload = function () {
          result.imgAuto = img.naturalWidth < img.naturalHeight;
          if (typeof createImageBitmap !== 'function') { result.bitmapOk = false; finish(); return; }
          try {
            createImageBitmap(blob, { imageOrientation: 'from-image' }).then(function (bm) {
              result.bitmapOk = bm.width < bm.height;
              if (bm.close) bm.close();
              finish();
            }, function () { result.bitmapOk = false; finish(); });
          } catch (e) { result.bitmapOk = false; finish(); }
        };
        img.onerror = finish;
        img.src = 'data:image/jpeg;base64,' + PROBE_JPEG;
      } catch (e) { finish(); }
    });
    return orientProbe;
  }

  // Primary path: createImageBitmap with orientation handling (only if the
  // probe proved the browser honours it). Fallback: decode via <img> and, only
  // if the browser does not auto-rotate, apply EXIF by hand.
  function decodeUpright(file) {
    return probeOrientationSupport().then(function (sup) {
      return new Promise(function (resolve, reject) {
        if (sup.bitmapOk) {
          var p;
          try {
            p = createImageBitmap(file, { imageOrientation: 'from-image' });
          } catch (e) {
            p = null;
          }
          if (p && typeof p.then === 'function') {
            p.then(function (bitmap) {
              var c = newCanvas(bitmap.width, bitmap.height);
              whiteCtx(c).drawImage(bitmap, 0, 0);
              if (bitmap.close) bitmap.close();
              resolve(c);
            }).catch(function () { decodeFallback(file, sup).then(resolve, reject); });
            return;
          }
        }
        decodeFallback(file, sup).then(resolve, reject);
      });
    });
  }

  function decodeFallback(file, sup) {
    // Browser already rotated the <img> -> treat as orientation 1 (no double rotation).
    var orientationP = (sup && sup.imgAuto) ? Promise.resolve(1) : readOrientationFromFile(file);
    return orientationP.then(function (orientation) {
      return new Promise(function (resolve, reject) {
        var url = URL.createObjectURL(file);
        var img = new Image();
        img.onload = function () {
          try {
            resolve(applyOrientation(img, img.naturalWidth, img.naturalHeight, orientation));
          } catch (e) {
            reject(e);
          } finally {
            URL.revokeObjectURL(url);
          }
        };
        img.onerror = function () { URL.revokeObjectURL(url); reject(new Error('decode')); };
        img.src = url;
      });
    });
  }

  function readOrientationFromFile(file) {
    return new Promise(function (resolve) {
      if (file.type !== 'image/jpeg' && !/\.jpe?g$/i.test(file.name || '')) { resolve(1); return; }
      var slice = file.slice(0, 128 * 1024);
      var reader = new FileReader();
      reader.onload = function () {
        var o = 1;
        try { o = readOrientation(reader.result); } catch (e) { o = 1; }
        resolve(o);
      };
      reader.onerror = function () { resolve(1); };
      reader.readAsArrayBuffer(slice);
    });
  }

  /* ---- 5. BORDER ANALYSIS ---- */

  // Runs on a downscaled working copy for speed. Result is cached per image.
  function analyzeBorder(source) {
    var longEdge = Math.max(source.width, source.height);
    var s = Math.min(1, WORK_LONG_EDGE / longEdge);
    var w = Math.max(1, Math.round(source.width * s));
    var h = Math.max(1, Math.round(source.height * s));

    var work = newCanvas(w, h);
    var wctx = whiteCtx(work);               // white first: transparency reads as white
    wctx.drawImage(source, 0, 0, w, h);

    var data;
    try {
      data = wctx.getImageData(0, 0, w, h).data;
    } catch (e) {
      return { variance: 0, r: 255, g: 255, b: 255, decision: 'white', color: '#ffffff' };
    }

    var band = Math.max(1, Math.round(Math.min(w, h) / 50));
    var sum = [0, 0, 0], sumSq = [0, 0, 0], n = 0;

    function take(x, y) {
      var i = (y * w + x) * 4;
      for (var c = 0; c < 3; c++) {
        var v = data[i + c];
        sum[c] += v;
        sumSq[c] += v * v;
      }
      n++;
    }

    // Simple non-deduped ring walk: corner pixels fall in two strips and are
    // counted twice. That does not materially change a mean/variance of a
    // border band, and keeps this loop trivial to read.
    var x, y;
    for (y = 0; y < band && y < h; y++) for (x = 0; x < w; x++) take(x, y);                 // top
    for (y = Math.max(0, h - band); y < h; y++) for (x = 0; x < w; x++) take(x, y);         // bottom
    for (x = 0; x < band && x < w; x++) for (y = 0; y < h; y++) take(x, y);                 // left
    for (x = Math.max(0, w - band); x < w; x++) for (y = 0; y < h; y++) take(x, y);         // right

    if (!n) n = 1;
    var mean = [sum[0] / n, sum[1] / n, sum[2] / n];
    var varc = [
      (sumSq[0] / n) - mean[0] * mean[0],
      (sumSq[1] / n) - mean[1] * mean[1],
      (sumSq[2] / n) - mean[2] * mean[2]
    ];
    var variance = (varc[0] + varc[1] + varc[2]) / 3;

    /* ---- 5.2 auto decision rule ---- */
    var decision;
    if (variance < VARIANCE_THRESHOLD) {
      decision = (mean[0] >= NEAR_WHITE_CUTOFF &&
                  mean[1] >= NEAR_WHITE_CUTOFF &&
                  mean[2] >= NEAR_WHITE_CUTOFF) ? 'white' : 'solid';
    } else {
      decision = 'blur';
    }

    return {
      variance: variance,
      r: mean[0], g: mean[1], b: mean[2],
      decision: decision,
      color: '#' + toHex(mean[0]) + toHex(mean[1]) + toHex(mean[2])
    };
  }

  function getAnalysis() {
    if (!state.source) return null;
    if (!state.analysis) state.analysis = analyzeBorder(state.source);
    return state.analysis;
  }

  // The mode actually used for rendering (resolves 'auto').
  function effectiveFill() {
    if (state.fill !== 'auto') return state.fill;
    var a = getAnalysis();
    return a ? a.decision : 'white';
  }

  // §5.3 snap-to-white: a near-white border prints as a faint visible rectangle
  // on an otherwise pure-white page. Applies to auto-solid and explicit solid.
  function solidColor() {
    if (state.customSolidColor) return state.customSolidColor;
    var a = getAnalysis();
    if (!a) return '#ffffff';
    if (a.r >= NEAR_WHITE_CUTOFF && a.g >= NEAR_WHITE_CUTOFF && a.b >= NEAR_WHITE_CUTOFF) {
      return '#ffffff';
    }
    return a.color;
  }

  /* ---- 6. GEOMETRY / LAYOUT MATH ---- */

  // ONE geometry function, used by both the preview (s < 1) and the export
  // (s === 1). Preview geometry is never computed independently, so preview
  // and export can never disagree.
  function computeGeometry(s) {
    var trim = TRIM_SIZES[state.trimIndex];
    var B = state.bleed ? BLEED_IN : 0;
    var M = state.margin;

    var canvasWin = trim.w + B * 2;
    var canvasHin = trim.h + B * 2;
    var fullW = Math.round(canvasWin * DPI);
    var fullH = Math.round(canvasHin * DPI);

    var bPx = B * DPI;
    var mPx = M * DPI;

    var trimRect = { x: bPx, y: bPx, w: fullW - bPx * 2, h: fullH - bPx * 2 };
    var safeRect = {
      x: bPx + mPx, y: bPx + mPx,
      w: Math.max(1, fullW - (bPx + mPx) * 2),
      h: Math.max(1, fullH - (bPx + mPx) * 2)
    };

    var geo = {
      scale: s,
      fullW: fullW, fullH: fullH,
      canvasWin: canvasWin, canvasHin: canvasHin,
      trimIn: trim,
      safeWin: Math.max(0, trim.w - M * 2),
      safeHin: Math.max(0, trim.h - M * 2),
      canvasW: Math.max(1, Math.round(fullW * s)),
      canvasH: Math.max(1, Math.round(fullH * s)),
      trim: scaleRect(trimRect, s),
      safe: scaleRect(safeRect, s),
      placed: null,
      fitScale: 1,
      fullPlacedW: 0,
      fullPlacedH: 0,
      blurRadius: Math.max(1, Math.round(0.03 * Math.max(fullW, fullH)))
    };

    if (state.source) {
      var imgW = state.source.width, imgH = state.source.height;
      // Fit, never fill: the artwork is never cropped and never distorted.
      // Not clamped to 1 — an undersized source is scaled up, and the DPI
      // readout is what tells the user about the consequence.
      var fit = Math.min(safeRect.w / imgW, safeRect.h / imgH);
      var placedW = imgW * fit;
      var placedH = imgH * fit;
      var placed = {
        x: safeRect.x + (safeRect.w - placedW) / 2,
        y: safeRect.y + (safeRect.h - placedH) / 2,
        w: placedW, h: placedH
      };
      geo.fitScale = fit;
      geo.fullPlacedW = placedW;
      geo.fullPlacedH = placedH;
      geo.placed = scaleRect(placed, s);

      // Cover: fills the WHOLE canvas edge-to-edge (real bleed), cropping
      // whatever overflows. Only the ring outside the safe area (bleed +
      // margin) is meant to be sacrificed — geo.coverRing/coverCropX/Y let
      // the UI warn when a mismatched aspect ratio would crop further in.
      var cover = Math.max(fullW / imgW, fullH / imgH);
      var coveredW = imgW * cover, coveredH = imgH * cover;
      var coverRect = {
        x: (fullW - coveredW) / 2, y: (fullH - coveredH) / 2,
        w: coveredW, h: coveredH
      };
      geo.coverScale = cover;
      geo.coverPlaced = scaleRect(coverRect, s);
      geo.fullCoverW = coveredW;
      geo.fullCoverH = coveredH;
      geo.coverCropX = Math.max(0, -coverRect.x);
      geo.coverCropY = Math.max(0, -coverRect.y);
      geo.coverRing = bPx + mPx;

      // Whichever placement mode is actually active drives the DPI reading
      // — Cover almost always uses a larger scale than Fit, so the quality
      // badge must reflect it, not silently keep the more optimistic number.
      var useCoverForDPI = state.bleed && state.bleedPlacement === 'cover';
      geo.effectiveDPI = DPI / (useCoverForDPI ? cover : fit);
    }
    return geo;
  }

  function scaleRect(r, s) {
    return { x: r.x * s, y: r.y * s, w: r.w * s, h: r.h * s };
  }

  /* ---- 7. RENDERING ---- */

  function supportsFilter(ctx) {
    if (typeof ctx.filter !== 'string') return false;
    ctx.filter = 'blur(2px)';
    var ok = ctx.filter !== 'none' && ctx.filter !== '';
    ctx.filter = 'none';
    return ok;
  }

  // Stepped downscale (§5.5): a single big drawImage aliases line art badly,
  // and aliasing is exactly what this tool's audience would notice first.
  // The halved levels are cached per image so dragging a control does not
  // rebuild the whole chain on every frame.
  function halfStep(src, dw) {
    if (!(dw > 0)) return src;
    if (!state.pyramid || state.pyramid[0] !== src) state.pyramid = [src];
    var levels = state.pyramid;
    var i = 0;
    while (levels[i].width > 1 && levels[i].width / 2 > dw) {
      if (!levels[i + 1]) {
        var prev = levels[i];
        var nw = Math.max(1, Math.floor(prev.width / 2));
        var nh = Math.max(1, Math.floor(prev.height / 2));
        var step = newCanvas(nw, nh);
        whiteCtx(step).drawImage(prev, 0, 0, nw, nh);
        levels[i + 1] = step;
      }
      i++;
    }
    return levels[i];
  }

  function drawArtwork(ctx, src, dx, dy, dw, dh) {
    smooth(ctx);
    ctx.drawImage(halfStep(src, dw), dx, dy, dw, dh);
  }

  // §5.4 — the blurred layer is a SECOND, cover-scaled copy used only as
  // background. It is cropped; the sharp copy the reader sees never is.
  function drawBlurBackground(ctx, src, w, h, r) {
    var pad = r * 2;                          // real pixels past every edge, so a
    var tw = w + pad * 2;                     // canvas blur at the rim has something
    var th = h + pad * 2;                     // to sample and does not fade/darken
    var tmp = newCanvas(tw, th);
    var tctx = whiteCtx(tmp);

    var cover = Math.max(tmp.width / src.width, tmp.height / src.height);
    var dw = src.width * cover, dh = src.height * cover;
    tctx.drawImage(src, (tmp.width - dw) / 2, (tmp.height - dh) / 2, dw, dh);

    if (r >= 1 && supportsFilter(ctx)) {
      ctx.filter = 'blur(' + r + 'px)';
      ctx.drawImage(tmp, -pad, -pad);
      ctx.filter = 'none';
      return;
    }

    // Fallback (old Safari): downscale-then-upscale, twice.
    var shrink = Math.max(1, Math.round(r / 2));
    var sw = Math.max(1, Math.round(tmp.width / shrink));
    var sh = Math.max(1, Math.round(tmp.height / shrink));
    var cur = tmp;
    for (var i = 0; i < 2; i++) {
      var small = newCanvas(sw, sh);
      whiteCtx(small).drawImage(cur, 0, 0, sw, sh);
      var big = newCanvas(tmp.width, tmp.height);
      whiteCtx(big).drawImage(small, 0, 0, tmp.width, tmp.height);
      cur = big;
    }
    ctx.drawImage(cur, -pad, -pad);
  }

  // Composes one page. `geo` carries its own scale, so this is identical for
  // preview and export. Guides are NOT drawn here — see section 8.
  function renderPage(ctx, geo) {
    ctx.save();
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.filter = 'none';
    ctx.fillStyle = '#ffffff';
    ctx.fillRect(0, 0, geo.canvasW, geo.canvasH);
    smooth(ctx);

    if (!state.source) { ctx.restore(); return; }

    var useCover = state.bleed && state.bleedPlacement === 'cover';

    if (!useCover) {
      var mode = effectiveFill();
      if (mode === 'solid') {
        ctx.fillStyle = solidColor();
        ctx.fillRect(0, 0, geo.canvasW, geo.canvasH);
      } else if (mode === 'blur') {
        var r = Math.max(1, Math.round(geo.blurRadius * geo.scale));
        drawBlurBackground(ctx, state.source, geo.canvasW, geo.canvasH, r);
      }
      // 'white' needs nothing further — the canvas is already pure white.
    }
    // Cover mode fills 100% of the canvas with artwork — there is no margin
    // left to fill, so the fill-mode branch above is skipped entirely.

    var p = useCover ? geo.coverPlaced : geo.placed;
    drawArtwork(ctx, state.source, p.x, p.y, p.w, p.h);
    ctx.restore();
  }

  /* ---- 8. PREVIEW & COMPARE SLIDER ---- */

  function schedulePreview() {
    if (previewRaf) return;
    previewRaf = requestAnimationFrame(function () {
      previewRaf = 0;
      renderPreview();
    });
  }

  function renderPreview() {
    updateReadout();
    if (!state.source) return;
    updateFillStepEnabled();
    updateCropWarning();

    var stageRect = el.stage.getBoundingClientRect();
    var availW = Math.max(40, stageRect.width - 32);
    var availH = Math.max(40, stageRect.height - 32);

    var geoFull = computeGeometry(1);
    var aspect = geoFull.fullW / geoFull.fullH;

    var dispH = availH, dispW = dispH * aspect;
    if (dispW > availW) { dispW = availW; dispH = dispW / aspect; }

    var dpr = Math.min(2, window.devicePixelRatio || 1);
    var longEdgeFull = Math.max(geoFull.fullW, geoFull.fullH);
    var previewScale = Math.min(
      1,
      PREVIEW_LONG_EDGE / longEdgeFull,
      (Math.max(dispW, dispH) * dpr) / longEdgeFull
    );

    var geo = computeGeometry(previewScale);

    el.sheet.style.width = dispW + 'px';
    el.sheet.style.height = dispH + 'px';

    if (el.previewCanvas.width !== geo.canvasW) el.previewCanvas.width = geo.canvasW;
    if (el.previewCanvas.height !== geo.canvasH) el.previewCanvas.height = geo.canvasH;
    renderPage(el.previewCanvas.getContext('2d'), geo);

    drawBefore(availW, availH, dpr);
    drawGuides(geo, dispW);
  }

  function drawBefore(availW, availH, dpr) {
    var src = state.source;
    var fit = Math.min(availW / src.width, availH / src.height);
    var cssW = src.width * fit, cssH = src.height * fit;
    var w = Math.max(1, Math.round(Math.min(cssW * dpr, PREVIEW_LONG_EDGE, src.width)));
    var h = Math.max(1, Math.round(w * (src.height / src.width)));

    var c = el.beforeCanvas;
    if (c.width !== w) c.width = w;
    if (c.height !== h) c.height = h;
    c.style.width = cssW + 'px';
    c.style.height = cssH + 'px';
    var ctx = whiteCtx(c);
    drawArtwork(ctx, src, 0, 0, w, h);
  }

  // Guides live on their own overlay canvas, drawn on top of the preview.
  // The export path (section 9) never calls this function — guides can
  // therefore never appear in the exported PNG.
  function drawGuides(geo, dispW) {
    var c = el.overlayCanvas;
    if (c.width !== geo.canvasW) c.width = geo.canvasW;
    if (c.height !== geo.canvasH) c.height = geo.canvasH;
    var ctx = c.getContext('2d');
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.clearRect(0, 0, c.width, c.height);
    if (!state.guides || !state.source) return;

    // px-per-CSS-px, so lines and labels keep their intended visual size
    var k = dispW > 0 ? (geo.canvasW / dispW) : 1;
    ctx.font = Math.round(10 * k) + 'px -apple-system, BlinkMacSystemFont, "Segoe UI", Roboto, Arial, sans-serif';
    ctx.textBaseline = 'top';

    // Trim line: only meaningful in Full bleed. Without bleed the trim line IS
    // the page edge, and drawing it is noise.
    if (state.bleed) {
      ctx.strokeStyle = '#94a3b8';
      ctx.setLineDash([]);
      ctx.lineWidth = 1 * k;
      ctx.strokeRect(geo.trim.x, geo.trim.y, geo.trim.w, geo.trim.h);
      ctx.fillStyle = '#94a3b8';
      ctx.fillText('TRIM', geo.trim.x + 3 * k, geo.trim.y + 3 * k);
    }

    ctx.strokeStyle = '#ea580c';
    ctx.setLineDash([6 * k, 5 * k]);
    ctx.lineWidth = 2 * k;
    ctx.strokeRect(geo.safe.x, geo.safe.y, geo.safe.w, geo.safe.h);
    ctx.setLineDash([]);
    ctx.fillStyle = '#ea580c';
    ctx.fillText('SAFE', geo.safe.x + 3 * k, geo.safe.y + 3 * k);
  }

  function setDivider(pct) {
    pct = Math.max(0, Math.min(100, pct));
    state.dividerPct = pct;
    el.divider.style.left = pct + '%';
    el.layerAfter.style.clipPath = 'inset(0 0 0 ' + pct + '%)';
    el.layerAfter.style.webkitClipPath = 'inset(0 0 0 ' + pct + '%)';
    el.handle.setAttribute('aria-valuenow', Math.round(pct));
    el.btnBefore.setAttribute('aria-pressed', pct >= 100 ? 'true' : 'false');
    el.btnBefore.classList.toggle('is-on', pct >= 100);
    el.btnAfter.setAttribute('aria-pressed', pct <= 0 ? 'true' : 'false');
    el.btnAfter.classList.toggle('is-on', pct <= 0);
  }

  function pointerToPct(clientX) {
    var r = el.compare.getBoundingClientRect();
    if (!r.width) return state.dividerPct;
    return ((clientX - r.left) / r.width) * 100;
  }

  /* ---- 9. EXPORT ---- */

  function exportFilename() {
    var t = TRIM_SIZES[state.trimIndex];
    var name = 'margin-fixed-' + fmtIn(t.w) + 'x' + fmtIn(t.h);
    if (t.note === 'A4') name += '-a4';
    if (state.bleed) name += '-bleed';
    return name + (state.format === 'jpg' ? '.jpg' : '.png');
  }

  function doExport() {
    if (!state.source || state.rendering) return;
    state.rendering = true;
    setDownloadBusy(true);

    // Let the busy state actually paint before the main thread blocks.
    requestAnimationFrame(function () {
      setTimeout(function () {
        try {
          var geo = computeGeometry(1);                 // same geometry function
          var canvas = newCanvas(geo.canvasW, geo.canvasH);
          renderPage(canvas.getContext('2d'), geo);     // no guide code path here

          canvas.toBlob(function (blob) {
            try {
              if (!blob) {
                showBanner('Something went wrong while creating the file. Please try again.');
                return;
              }
              var url = URL.createObjectURL(blob);
              var a = document.createElement('a');
              a.href = url;
              a.download = exportFilename();
              document.body.appendChild(a);
              a.click();
              document.body.removeChild(a);
              setTimeout(function () { URL.revokeObjectURL(url); }, 0);
              showToast(exportFilename(), geo.canvasW, geo.canvasH);
            } finally {
              state.rendering = false;
              setDownloadBusy(false);
            }
          }, state.format === 'jpg' ? 'image/jpeg' : 'image/png',
             state.format === 'jpg' ? JPEG_QUALITY : undefined);
        } catch (e) {
          showBanner('Something went wrong while creating the file. Please try again.');
          state.rendering = false;
          setDownloadBusy(false);
        }
      }, 0);
    });
  }

  function setDownloadBusy(busy) {
    el.downloadBtn.disabled = busy || !state.source;
    if (busy) {
      el.downloadBtn.innerHTML = '<span class="spinner" aria-hidden="true"></span><span>Rendering…</span>';
    } else {
      el.downloadBtn.innerHTML = '<span>Download ' + (state.format === 'jpg' ? 'JPG' : 'PNG') + '</span>';
    }
  }

  function showToast(name, w, h) {
    el.toast.innerHTML = '';
    var strong = document.createElement('strong');
    strong.textContent = 'Saved! ';
    el.toast.appendChild(strong);
    el.toast.appendChild(document.createTextNode(
      '"' + name + '" — ' + w + ' × ' + h + ' px, ready for KDP.'));
    el.toast.hidden = false;
    clearTimeout(toastTimer);
    toastTimer = setTimeout(function () { el.toast.hidden = true; }, 5000);
  }

  /* ---- 10. UI WIRING ---- */

  function buildTrimOptions() {
    var groups = {};
    var order = [];
    TRIM_SIZES.forEach(function (t, i) {
      if (!groups[t.group]) { groups[t.group] = []; order.push(t.group); }
      groups[t.group].push(i);
    });
    order.forEach(function (g) {
      var og = document.createElement('optgroup');
      og.label = g;
      groups[g].forEach(function (i) {
        var t = TRIM_SIZES[i];
        // At 300 DPI every official size lands on a whole pixel.
        var px = Math.round(t.w * DPI) + ' × ' + Math.round(t.h * DPI) + ' px';
        var o = document.createElement('option');
        o.value = String(i);
        o.textContent = trimLabelInches(t) + (t.note ? ' (' + t.note + ')' : '') + ' — ' + px;
        og.appendChild(o);
      });
      el.trimSelect.appendChild(og);
    });
    el.trimSelect.value = String(DEFAULT_TRIM_INDEX);
  }

  function showBanner(message, actionLabel, onAction) {
    el.bannerHost.innerHTML = '';
    var box = document.createElement('div');
    box.className = 'banner';

    var body = document.createElement('div');
    body.className = 'banner-body';
    var p = document.createElement('p');
    p.textContent = message;
    body.appendChild(p);

    if (actionLabel) {
      var act = document.createElement('button');
      act.type = 'button';
      act.className = 'link-btn';
      act.style.marginTop = '6px';
      act.textContent = actionLabel;
      act.addEventListener('click', function () {
        el.bannerHost.innerHTML = '';
        onAction();
      });
      body.appendChild(act);
    }

    var x = document.createElement('button');
    x.type = 'button';
    x.className = 'banner-x';
    x.setAttribute('aria-label', 'Dismiss');
    x.innerHTML = '&times;';
    x.addEventListener('click', function () {
      state.pendingBigFile = null;
      el.bannerHost.innerHTML = '';
    });

    box.appendChild(body);
    box.appendChild(x);
    el.bannerHost.appendChild(box);
  }

  function onImageReady() {
    el.bannerHost.innerHTML = '';
    el.emptyState.hidden = true;
    el.emptyPrivacy.hidden = true;
    el.compare.hidden = false;
    el.chooseBtn.hidden = true;
    el.fileInfo.hidden = false;
    el.fileInfoText.textContent = state.fileName + ' · ' +
      state.source.width + ' × ' + state.source.height + ' px · ' +
      fmtFileSize(state.fileSize);

    setStepsEnabled(true);
    el.downloadBtn.disabled = false;
    el.downloadBtn.removeAttribute('title');

    refreshFillUI();
    setDivider(state.dividerPct);
    schedulePreview();
  }

  // Steps 2-4 stay dimmed until there is an image. Dimming alone would still
  // leave the controls tabbable, so they are genuinely disabled too.
  function setStepsEnabled(on) {
    ['step2', 'step3', 'step4', 'stepFormat'].forEach(function (id) {
      $(id).classList.toggle('locked', !on);
    });
    [el.trimSelect, el.bleedOn, el.bleedOff, el.placementCover, el.placementFit,
     el.marginSelect, el.marginCustom, el.fillSelect, el.fmtPng, el.fmtJpg].forEach(function (c) { c.disabled = !on; });
  }

  function setFormat(fmt) {
    state.format = fmt;
    el.fmtPng.classList.toggle('is-on', fmt === 'png');
    el.fmtPng.setAttribute('aria-pressed', fmt === 'png' ? 'true' : 'false');
    el.fmtJpg.classList.toggle('is-on', fmt === 'jpg');
    el.fmtJpg.setAttribute('aria-pressed', fmt === 'jpg' ? 'true' : 'false');
    el.formatHint.textContent = FORMAT_HINTS[fmt];
    if (!state.rendering) setDownloadBusy(false);   // refreshes the button label
  }

  function refreshFillUI() {
    updateAutoChip();
    updateSolidColorRow();
  }

  function updateAutoChip() {
    if (state.fill !== 'auto' || !state.source) { el.autoChip.hidden = true; return; }
    var d = effectiveFill();
    el.autoChip.hidden = false;
    el.autoChip.innerHTML = '';
    if (d === 'white') {
      el.autoChip.textContent = 'Auto chose: White';
    } else if (d === 'blur') {
      el.autoChip.textContent = 'Auto chose: Blur';
    } else {
      var col = solidColor();
      el.autoChip.appendChild(document.createTextNode('Auto chose: Solid ' + col));
      var sw = document.createElement('span');
      sw.className = 'swatch';
      sw.style.background = col;
      el.autoChip.appendChild(sw);
    }
  }

  // Shows/hides the "Pick color" row — only relevant in explicit Solid mode
  // (not Auto, even when Auto resolves to solid; picking a color is a
  // deliberate override, not something Auto should surface).
  function updateSolidColorRow() {
    var show = state.fill === 'solid' && !!state.source;
    el.solidColorRow.hidden = !show;
    if (!show) return;
    var col = solidColor();
    el.colorSwatchPreview.style.background = col;
    el.colorSwatchLabel.textContent = state.customSolidColor ? col : 'Pick color';
    el.colorResetBtn.hidden = !state.customSolidColor;
  }

  function updateMarginWarning() {
    var msg = '';
    if (state.bleed && state.margin < MIN_MARGIN_BLEED) {
      msg = 'KDP requires at least 0.375" from the trim edge on bleed pages.';
    } else if (!state.bleed && state.margin < MIN_MARGIN_NO_BLEED) {
      msg = 'KDP requires at least 0.25" from the page edge.';
    }
    el.marginWarn.hidden = !msg;
    el.marginWarn.textContent = msg;
  }

  function updateReadout() {
    var geo = computeGeometry(1);
    var t = geo.trimIn;

    el.outMain.textContent = 'Output: ' + geo.fullW + ' × ' + geo.fullH + ' px  ·  ' +
      fmtIn(geo.canvasWin) + '" × ' + fmtIn(geo.canvasHin) + '"  ·  300 DPI';
    el.outSub.textContent = state.bleed
      ? 'Trim size ' + trimLabelInches(t) + ' + 0.125" bleed all round' +
        (state.bleedPlacement === 'cover' ? ' · edge-to-edge' : ' · whole image kept')
      : 'Trim size ' + trimLabelInches(t) + ', no bleed';

    if (state.source) {
      var useCoverNow = state.bleed && state.bleedPlacement === 'cover';
      var placedW = useCoverNow ? geo.fullCoverW : geo.fullPlacedW;
      var placedH = useCoverNow ? geo.fullCoverH : geo.fullPlacedH;
      el.outSafe.textContent = 'Safe area: ' + fmtIn(geo.safeWin) + '" × ' + fmtIn(geo.safeHin) +
        '"  ·  artwork placed at ' + Math.round(placedW) + ' × ' +
        Math.round(placedH) + ' px';
      updateQuality(Math.round(geo.effectiveDPI));
    } else {
      el.outSafe.textContent = 'Safe area: ' + fmtIn(geo.safeWin) + '" × ' + fmtIn(geo.safeHin) + '"';
      el.quality.hidden = true;
    }
  }

  function updateQuality(dpi) {
    el.quality.hidden = false;
    el.quality.className = 'quality';
    el.qCopy.innerHTML = '';
    if (dpi >= 300) {
      el.quality.classList.add('q-ok');
      el.qTitle.textContent = '✅ Print quality: Excellent';
      el.qCopy.textContent = 'Your image is sharp enough for print at this size (' + dpi + ' DPI).';
    } else if (dpi >= 200) {
      el.quality.classList.add('q-warn');
      el.qTitle.textContent = '⚠️ Print quality: Acceptable';
      el.qCopy.textContent = 'At ' + dpi + ' DPI this will print a little soft. Fine for most coloring pages, but a larger original would look crisper.';
    } else {
      el.quality.classList.add('q-bad');
      el.qTitle.textContent = '⛔ Print quality: Low';
      el.qCopy.textContent = 'At ' + dpi + ' DPI this is likely to look blurry in print. Try starting from a larger version of your image.';
    }
  }

  // Cover fills the whole canvas — there is no margin left for Step 4's
  // fill style to apply to, so it's disabled (not hidden) with an
  // explanatory hint while Cover is active, and restored when it isn't.
  function updateFillStepEnabled() {
    if (!state.source) return;
    var coverActive = state.bleed && state.bleedPlacement === 'cover';
    el.fillSelect.disabled = coverActive;
    if (coverActive) {
      el.fillHint.textContent = 'Not needed — your artwork fills the whole page edge-to-edge in this mode.';
      el.autoChip.hidden = true;
      el.solidColorRow.hidden = true;
    } else {
      el.fillHint.textContent = FILL_HINTS[state.fill];
      refreshFillUI();
    }
  }

  // Warns when the source image's aspect ratio is different enough from the
  // page's that Cover would crop past the sacrificial bleed+margin ring and
  // into the safe area itself — i.e. into content the user was told is safe.
  function updateCropWarning() {
    var coverActive = state.bleed && state.bleedPlacement === 'cover';
    if (!coverActive || !state.source) { el.cropWarn.hidden = true; return; }
    var geo = computeGeometry(1);
    var tooMuch = geo.coverCropX > geo.coverRing + 1 || geo.coverCropY > geo.coverRing + 1;
    el.cropWarn.hidden = !tooMuch;
    if (tooMuch) {
      el.cropWarn.textContent = 'Your image’s shape is quite different from this page’s shape, so Extend to edge would crop into your artwork, not just the outer edge. Consider "Keep whole image" instead.';
    }
  }

  function setBleedPlacement(mode) {
    state.bleedPlacement = mode;
    el.placementCover.classList.toggle('is-on', mode === 'cover');
    el.placementCover.setAttribute('aria-pressed', mode === 'cover' ? 'true' : 'false');
    el.placementFit.classList.toggle('is-on', mode === 'fit');
    el.placementFit.setAttribute('aria-pressed', mode === 'fit' ? 'true' : 'false');
    el.placementHint.textContent = mode === 'cover' ? PLACEMENT_HINTS.cover : PLACEMENT_HINTS.fit;
    updateFillStepEnabled();
    updateCropWarning();
    schedulePreview();
  }

  function setBleed(on) {
    state.bleed = on;
    el.bleedOn.classList.toggle('is-on', on);
    el.bleedOn.setAttribute('aria-pressed', on ? 'true' : 'false');
    el.bleedOff.classList.toggle('is-on', !on);
    el.bleedOff.setAttribute('aria-pressed', on ? 'false' : 'true');
    el.bleedHint.textContent = on ? BLEED_HINTS.on : BLEED_HINTS.off;
    el.bleedPlacementField.hidden = !on;
    if (on) {
      setBleedPlacement('cover');   // Cover is what "Full bleed" should mean by default
    } else {
      updateFillStepEnabled();
      updateCropWarning();
    }

    // Only move the margin if the user has not made a deliberate choice, or if
    // their current value is now below the KDP minimum for the new mode.
    var min = on ? MIN_MARGIN_BLEED : MIN_MARGIN_NO_BLEED;
    if (!state.marginTouched || state.margin < min) {
      applyMargin(min, false);
      el.marginSelect.value = String(min);
      el.customRow.hidden = true;
      state.marginMode = String(min);
    }
    updateMarginWarning();
    schedulePreview();
  }

  function applyMargin(value, touched) {
    state.margin = value;
    if (touched) state.marginTouched = true;
    updateMarginWarning();
  }

  function onMarginSelect() {
    var v = el.marginSelect.value;
    state.marginMode = v;
    if (v === 'custom') {
      el.customRow.hidden = false;
      var cv = parseFloat(el.marginCustom.value);
      if (!isFinite(cv)) { cv = state.margin; el.marginCustom.value = fmtIn(cv); }
      applyMargin(clampMargin(cv), true);
      el.marginCustom.focus();
    } else {
      el.customRow.hidden = true;
      applyMargin(parseFloat(v), true);
    }
    schedulePreview();
  }

  function clampMargin(v) { return Math.max(0, Math.min(1, v)); }

  function onCustomInput() {
    clearTimeout(marginDebounce);
    marginDebounce = setTimeout(function () {
      var raw = el.marginCustom.value;
      var v = parseFloat(raw);
      if (raw === '' || !isFinite(v)) {
        showBanner('Please enter a margin as a number between 0 and 1 inches — for example 0.35.');
        return;
      }
      el.bannerHost.innerHTML = '';
      applyMargin(clampMargin(v), true);
      schedulePreview();
    }, 150);
  }

  function onCustomBlur() {
    var raw = el.marginCustom.value;
    var v = parseFloat(raw);
    if (raw === '' || !isFinite(v)) {
      el.marginCustom.value = fmtIn(state.margin);
      showBanner('Please enter a margin as a number between 0 and 1 inches — for example 0.35.');
      return;
    }
    v = clampMargin(v);
    el.marginCustom.value = fmtIn(v);
    el.bannerHost.innerHTML = '';
    applyMargin(v, true);
    schedulePreview();
  }

  function closePopovers(except) {
    [['help2', 'pop2'], ['help3', 'pop3'], ['help4', 'pop4']].forEach(function (pair) {
      if (pair[1] === except) return;
      $(pair[1]).hidden = true;
      $(pair[0]).setAttribute('aria-expanded', 'false');
    });
  }

  function wirePopover(btnId, popId) {
    var btn = $(btnId), pop = $(popId);
    btn.addEventListener('click', function (e) {
      e.stopPropagation();
      var open = pop.hidden;
      closePopovers(open ? popId : null);
      pop.hidden = !open;
      btn.setAttribute('aria-expanded', open ? 'true' : 'false');
    });
    pop.addEventListener('click', function (e) { e.stopPropagation(); });
  }

  function openPicker() { el.fileInput.click(); }

  // EyeDropper samples any pixel on screen — Chrome/Edge only. Firefox/Safari
  // fall back to the native <input type="color"> swatch picker (can't sample
  // the page, but still lets the user choose any color by hand).
  function openColorPicker() {
    if (typeof window.EyeDropper === 'function') {
      new window.EyeDropper().open().then(function (result) {
        state.customSolidColor = result.sRGBHex;
        refreshFillUI();
        schedulePreview();
      }).catch(function () { /* user cancelled — no-op */ });
      return;
    }
    el.colorFallbackInput.value = solidColor();
    el.colorFallbackInput.click();
  }

  function init() {
    // cache DOM
    ['bannerHost', 'chooseBtn', 'fileInput', 'fileInfo', 'fileInfoText', 'replaceBtn',
     'fmtPng', 'fmtJpg', 'formatHint',
     'trimSelect', 'bleedOn', 'bleedOff', 'bleedHint',
     'bleedPlacementField', 'placementCover', 'placementFit', 'placementHint', 'cropWarn',
     'marginSelect', 'customRow',
     'marginCustom', 'marginWarn', 'fillSelect', 'fillHint', 'autoChip', 'downloadBtn',
     'solidColorRow', 'colorSwatchBtn', 'colorSwatchPreview', 'colorSwatchLabel',
     'colorResetBtn', 'colorFallbackInput',
     'guidesToggle', 'stage', 'emptyState', 'emptyPrivacy', 'compare', 'beforeCanvas',
     'layerAfter', 'sheet', 'previewCanvas', 'overlayCanvas', 'divider', 'handle',
     'btnBefore', 'btnAfter', 'toast', 'outMain', 'outSub', 'outSafe', 'quality',
     'qTitle', 'qCopy'].forEach(function (id) { el[id] = $(id); });

    buildTrimOptions();
    setStepsEnabled(false);
    setDivider(50);
    updateMarginWarning();
    updateReadout();

    /* -- step 1: upload -- */
    el.chooseBtn.addEventListener('click', openPicker);
    el.replaceBtn.addEventListener('click', openPicker);
    el.fileInput.addEventListener('change', function () {
      handleFiles(el.fileInput.files);
      el.fileInput.value = '';                 // allow re-picking the same file
    });

    el.emptyState.addEventListener('click', openPicker);
    el.emptyState.addEventListener('keydown', function (e) {
      if (e.key === 'Enter' || e.key === ' ' || e.key === 'Spacebar') {
        e.preventDefault();
        openPicker();
      }
    });

    // A stray drop must never navigate away from the page.
    window.addEventListener('dragover', function (e) { e.preventDefault(); });
    window.addEventListener('drop', function (e) { e.preventDefault(); });

    el.stage.addEventListener('dragover', function (e) {
      e.preventDefault();
      el.stage.classList.add('dragover');
    });
    el.stage.addEventListener('dragleave', function () { el.stage.classList.remove('dragover'); });
    el.stage.addEventListener('drop', function (e) {
      e.preventDefault();
      el.stage.classList.remove('dragover');
      if (e.dataTransfer && e.dataTransfer.files) handleFiles(e.dataTransfer.files);
    });

    document.addEventListener('paste', function (e) {
      if (e.clipboardData && e.clipboardData.files && e.clipboardData.files.length) {
        handleFiles(e.clipboardData.files);
      }
    });

    /* -- step 2: trim size -- */
    el.trimSelect.addEventListener('change', function () {
      state.trimIndex = parseInt(el.trimSelect.value, 10) || 0;
      schedulePreview();
    });

    /* -- step 3: bleed + margin -- */
    el.bleedOff.addEventListener('click', function () { setBleed(false); });
    el.bleedOn.addEventListener('click', function () { setBleed(true); });
    el.placementCover.addEventListener('click', function () { setBleedPlacement('cover'); });
    el.placementFit.addEventListener('click', function () { setBleedPlacement('fit'); });
    el.marginSelect.addEventListener('change', onMarginSelect);
    el.marginCustom.addEventListener('input', onCustomInput);
    el.marginCustom.addEventListener('blur', onCustomBlur);

    /* -- step 4: fill -- */
    el.fillSelect.addEventListener('change', function () {
      state.fill = el.fillSelect.value;
      el.fillHint.textContent = FILL_HINTS[state.fill];
      refreshFillUI();
      schedulePreview();
    });

    el.colorSwatchBtn.addEventListener('click', openColorPicker);
    el.colorFallbackInput.addEventListener('input', function () {
      state.customSolidColor = el.colorFallbackInput.value;
      refreshFillUI();
      schedulePreview();
    });
    el.colorResetBtn.addEventListener('click', function () {
      state.customSolidColor = null;
      refreshFillUI();
      schedulePreview();
    });

    /* -- save-as format -- */
    el.fmtPng.addEventListener('click', function () { setFormat('png'); });
    el.fmtJpg.addEventListener('click', function () { setFormat('jpg'); });

    /* -- tooltips -- */
    wirePopover('help2', 'pop2');
    wirePopover('help3', 'pop3');
    wirePopover('help4', 'pop4');
    document.addEventListener('click', function () { closePopovers(null); });
    document.addEventListener('keydown', function (e) {
      if (e.key === 'Escape') closePopovers(null);
    });

    /* -- preview toolbar -- */
    el.guidesToggle.addEventListener('change', function () {
      state.guides = el.guidesToggle.checked;
      schedulePreview();
    });
    el.btnBefore.addEventListener('click', function () { setDivider(100); });
    el.btnAfter.addEventListener('click', function () { setDivider(0); });

    /* -- compare divider -- */
    var dragging = false;
    el.handle.addEventListener('pointerdown', function (e) {
      dragging = true;
      if (el.handle.setPointerCapture) el.handle.setPointerCapture(e.pointerId);
      e.preventDefault();
    });
    el.handle.addEventListener('pointermove', function (e) {
      if (!dragging) return;
      setDivider(pointerToPct(e.clientX));
    });
    function endDrag(e) {
      if (!dragging) return;
      dragging = false;
      if (el.handle.releasePointerCapture && e.pointerId !== undefined) {
        try { el.handle.releasePointerCapture(e.pointerId); } catch (err) { /* ignore */ }
      }
    }
    el.handle.addEventListener('pointerup', endDrag);
    el.handle.addEventListener('pointercancel', endDrag);
    el.handle.addEventListener('keydown', function (e) {
      var p = state.dividerPct;
      if (e.key === 'ArrowLeft') { setDivider(p - 2); e.preventDefault(); }
      else if (e.key === 'ArrowRight') { setDivider(p + 2); e.preventDefault(); }
      else if (e.key === 'Home') { setDivider(0); e.preventDefault(); }
      else if (e.key === 'End') { setDivider(100); e.preventDefault(); }
    });

    /* -- export -- */
    el.downloadBtn.addEventListener('click', doExport);

    /* -- responsive re-render -- */
    window.addEventListener('resize', function () {
      clearTimeout(resizeDebounce);
      resizeDebounce = setTimeout(schedulePreview, 120);
    });
  }

  if (document.readyState === 'loading') {
    document.addEventListener('DOMContentLoaded', init);
  } else {
    init();
  }

})();
