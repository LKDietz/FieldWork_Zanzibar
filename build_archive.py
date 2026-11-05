#!/usr/bin/env python3
"""
build_archive.py  -  turn a folder of photos/videos + Strava GPX files into the data
file that index.html reads.

Folder layout (all paths relative to this script):
    media/      your photos and videos (any sub-folders are fine)
    tracks/     your Strava .gpx files
    data/       written by this script: archive.js
                (notes.js is created once and never overwritten: your places + sketches)
                overrides.csv (optional): file,lat,lon[,note]  fixes a wrong or missing location
    thumbs/     written by this script: small preview images

Usage:
    python3 build_archive.py                 # normal run
    python3 build_archive.py --tz +03:00     # timezone to assume when a file has no offset (default EAT)
    python3 build_archive.py --track-tol 90  # max seconds between a GPS-less file and the track
    python3 build_archive.py --clock-offset 0   # seconds to ADD to camera time before matching to the track

Needs: Python 3.9+, Pillow (pip install pillow). Optional: pillow-heif for .HEIC photos
(pip install pillow-heif), and ffmpeg/ffprobe on your PATH for videos (brew install ffmpeg).
"""
import argparse
import bisect
import csv
import datetime as dt
import hashlib
import json
import math
import re
import subprocess
import sys
import xml.etree.ElementTree as ET
from pathlib import Path

ROOT = Path(__file__).resolve().parent
PHOTO_EXT = {".jpg", ".jpeg", ".png", ".heic", ".heif"}
VIDEO_EXT = {".mov", ".mp4", ".m4v"}
# Okabe-Ito: distinguishable for most kinds of colour blindness. One colour per day.
PALETTE = ["#D55E00", "#0072B2", "#009E73", "#CC79A7", "#E69F00", "#56B4E9", "#7A7A7A", "#B8860B"]

try:
    from PIL import Image, ImageOps
except ImportError:
    sys.exit("Pillow is missing. Run:  pip install pillow")
try:
    import pillow_heif  # noqa
    pillow_heif.register_heif_opener()
    HEIF = True
except Exception:
    HEIF = False


# ---------------------------------------------------------------- helpers
def parse_tz(s):
    m = re.fullmatch(r"([+-])(\d{2}):?(\d{2})", s)
    if not m:
        sys.exit("--tz must look like +03:00")
    sign = 1 if m.group(1) == "+" else -1
    return dt.timezone(sign * dt.timedelta(hours=int(m.group(2)), minutes=int(m.group(3))))


def parse_offset(s):
    if not s:
        return None
    m = re.fullmatch(r"\s*([+-])(\d{2}):?(\d{2})\s*", s)
    if not m:
        return None
    sign = 1 if m.group(1) == "+" else -1
    return dt.timezone(sign * dt.timedelta(hours=int(m.group(2)), minutes=int(m.group(3))))


def parse_iso(s):
    s = s.strip().replace("Z", "+00:00")
    # +0300 -> +03:00
    s = re.sub(r"([+-]\d{2})(\d{2})$", r"\1:\2", s)
    return dt.datetime.fromisoformat(s)


def metres(lat1, lon1, lat2, lon2):
    return math.hypot((lat1 - lat2) * 110574, (lon1 - lon2) * 111320 * math.cos(math.radians((lat1 + lat2) / 2)))


def rat(x):
    try:
        return float(x)
    except Exception:
        return float(x[0]) / float(x[1])


def dms(v, ref):
    d = rat(v[0]) + rat(v[1]) / 60 + rat(v[2]) / 3600
    return -d if ref in ("S", "W") else d


# ---------------------------------------------------------------- readers
def read_photo(path, default_tz):
    out = {"t": None, "lat": None, "lon": None, "acc": None, "tsrc": "exif"}
    with Image.open(path) as im:
        ex = im.getexif()
        sub = ex.get_ifd(0x8769)
        gps = ex.get_ifd(0x8825)
        raw = sub.get(36867) or sub.get(36868) or ex.get(306)
        if raw:
            naive = dt.datetime.strptime(re.sub(r"^(\d{4})[-:](\d{2})[-:](\d{2})", r"\1:\2:\3", str(raw).strip()), "%Y:%m:%d %H:%M:%S")
            off = parse_offset(str(sub.get(36881) or sub.get(36880) or ""))
            if off is None and gps.get(29) and gps.get(7):  # GPS date + time are UTC
                try:
                    h, m, s = (rat(x) for x in gps[7])
                    utc = dt.datetime.strptime(str(gps[29]), "%Y:%m:%d").replace(
                        hour=int(h), minute=int(m), second=int(s), tzinfo=dt.timezone.utc)
                    off = dt.timezone(dt.timedelta(seconds=round((naive - utc.replace(tzinfo=None)).total_seconds() / 900) * 900))
                except Exception:
                    off = None
            if off is None:
                off = default_tz
                out["tsrc"] = "assumed-tz"
            out["t"] = naive.replace(tzinfo=off)
        if gps.get(2) and gps.get(4):
            try:
                out["lat"] = dms(gps[2], gps.get(1, "N"))
                out["lon"] = dms(gps[4], gps.get(3, "E"))
                if gps.get(31) is not None:
                    out["acc"] = round(rat(gps[31]), 1)
            except Exception:
                pass
    return out


def run_ffprobe(path):
    r = subprocess.run(["ffprobe", "-v", "error", "-print_format", "json", "-show_format", "-show_streams", str(path)],
                       capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(r.stderr.strip()[:200])
    return json.loads(r.stdout)


def read_video(path, default_tz):
    out = {"t": None, "lat": None, "lon": None, "acc": None, "tsrc": "quicktime", "dur": None}
    info = run_ffprobe(path)
    tags = {k.lower(): v for k, v in (info.get("format", {}).get("tags") or {}).items()}
    out["dur"] = round(float(info["format"].get("duration", 0)), 1)
    cd = tags.get("com.apple.quicktime.creationdate")
    if cd:
        out["t"] = parse_iso(cd)
    elif tags.get("creation_time"):
        out["t"] = parse_iso(tags["creation_time"])  # UTC; may be the export date, not the capture date
        out["tsrc"] = "creation_time-fallback"
    iso = tags.get("com.apple.quicktime.location.iso6709") or tags.get("location")
    if iso:
        m = re.match(r"([+-]\d+(?:\.\d+)?)([+-]\d+(?:\.\d+)?)", iso)
        if m:
            out["lat"], out["lon"] = float(m.group(1)), float(m.group(2))
    a = tags.get("com.apple.quicktime.location.accuracy.horizontal")
    if a:
        out["acc"] = round(float(a), 1)
    return out


def thumb(src, dst, kind, dur=None):
    dst.parent.mkdir(exist_ok=True)
    if dst.exists():
        return True
    try:
        if kind == "photo":
            with Image.open(src) as im:
                im = ImageOps.exif_transpose(im).convert("RGB")
                im.thumbnail((360, 360))
                im.save(dst, "JPEG", quality=78)
            return True
        ss = min(0.5, (dur or 1) / 2)
        r = subprocess.run(["ffmpeg", "-v", "error", "-y", "-ss", str(ss), "-i", str(src), "-frames:v", "1",
                            "-vf", "scale=360:-2", str(dst)], capture_output=True)
        return r.returncode == 0 and dst.exists()
    except Exception:
        return False


# ---------------------------------------------------------------- tracks
def read_gpx(path, tz, thin_m=3.0):
    root = ET.parse(path).getroot()
    pts = []
    for p in root.iter():
        if p.tag.endswith("}trkpt") or p.tag == "trkpt":
            t = None
            for ch in p:
                if ch.tag.endswith("time"):
                    t = parse_iso(ch.text)
            if t is None:
                continue
            pts.append((float(p.get("lat")), float(p.get("lon")), t.timestamp()))
    pts.sort(key=lambda x: x[2])
    kept = []
    for p in pts:
        if not kept or metres(p[0], p[1], kept[-1][0], kept[-1][1]) > thin_m or p[2] - kept[-1][2] > 30:
            kept.append(p)
    if pts and kept[-1] != pts[-1]:
        kept.append(pts[-1])
    name = path.stem
    day = dt.datetime.fromtimestamp(pts[0][2], tz).strftime("%Y-%m-%d") if pts else None
    return {"name": name, "day": day, "n_raw": len(pts),
            "start": dt.datetime.fromtimestamp(pts[0][2], tz).isoformat(timespec="seconds") if pts else None,
            "end": dt.datetime.fromtimestamp(pts[-1][2], tz).isoformat(timespec="seconds") if pts else None,
            "pts": [[round(a, 6), round(b, 6), int(c)] for a, b, c in kept]}


def locate_on_tracks(ts, tracks, tol):
    """Linear interpolation of position at epoch ts; None if no track is within tol seconds."""
    best = None
    for tr in tracks:
        pts = tr["pts"]
        times = [p[2] for p in pts]
        if not pts or ts < times[0] - tol or ts > times[-1] + tol:
            continue
        i = bisect.bisect_left(times, ts)
        if i == 0:
            cand = (pts[0][0], pts[0][1], abs(ts - times[0]))
        elif i >= len(pts):
            cand = (pts[-1][0], pts[-1][1], abs(ts - times[-1]))
        else:
            a, b = pts[i - 1], pts[i]
            gap = min(ts - a[2], b[2] - ts)
            f = (ts - a[2]) / (b[2] - a[2]) if b[2] != a[2] else 0
            cand = (a[0] + f * (b[0] - a[0]), a[1] + f * (b[1] - a[1]), gap)
        if cand[2] <= tol and (best is None or cand[2] < best[2]):
            best = cand
    return best


# ---------------------------------------------------------------- main
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--media", default="media")
    ap.add_argument("--tracks", default="tracks")
    ap.add_argument("--tz", default="+03:00")
    ap.add_argument("--track-tol", type=float, default=90)
    ap.add_argument("--clock-offset", type=float, default=0)
    ap.add_argument("--no-thumbs", action="store_true")
    ap.add_argument("--export-spot", action="append", metavar="LAT,LON",
                    help="copy all media within --radius of this point into export/<name>/ (repeat for several points)")
    ap.add_argument("--radius", type=float, default=60, help="metres around each --export-spot (default 60)")
    ap.add_argument("--name", default="site", help="folder name for the export")
    ap.add_argument("--max-per-day", type=int, default=0, help="if set, keep an even sample of at most N items per day")
    ap.add_argument("--small", action="store_true", help="export lighter copies: photos max 1280 px, videos 540 px high")
    ap.add_argument("--dry-run", action="store_true", help="only count, do not copy")
    a = ap.parse_args()
    if a.export_spot:
        return export_spots(a)
    tz = parse_tz(a.tz)
    media_dir, track_dir = ROOT / a.media, ROOT / a.tracks
    (ROOT / "data").mkdir(exist_ok=True)

    have_ffprobe = subprocess.run(["which", "ffprobe"], capture_output=True).returncode == 0 if sys.platform != "win32" else True
    # tracks
    tracks = []
    for g in sorted(track_dir.glob("**/*.gpx")) if track_dir.exists() else []:
        try:
            tr = read_gpx(g, tz)
            if tr["pts"]:
                tracks.append(tr)
        except Exception as e:
            print(f"  ! could not read {g.name}: {e}")
    print(f"tracks: {len(tracks)}")

    # overrides
    overrides = {}
    ov = ROOT / "data" / "overrides.csv"
    if ov.exists():
        with open(ov, newline="", encoding="utf-8") as f:
            for row in csv.reader(f):
                if len(row) >= 3 and not row[0].startswith("#"):
                    try:
                        overrides[row[0].strip()] = (float(row[1]), float(row[2]))
                    except ValueError:
                        pass

    files = sorted(p for p in media_dir.glob("**/*") if p.suffix.lower() in PHOTO_EXT | VIDEO_EXT) if media_dir.exists() else []
    print(f"media files found: {len(files)}")
    media, problems = [], []
    for i, p in enumerate(files, 1):
        kind = "photo" if p.suffix.lower() in PHOTO_EXT else "video"
        rel = p.relative_to(ROOT).as_posix()
        try:
            if kind == "photo":
                if p.suffix.lower() in (".heic", ".heif") and not HEIF:
                    raise RuntimeError("HEIC needs: pip install pillow-heif")
                m = read_photo(p, tz)
            else:
                m = read_video(p, tz)
        except Exception as e:
            problems.append((rel, f"unreadable: {e}"))
            continue
        if m["t"] is None:
            problems.append((rel, "no capture time found"))
            continue
        t = m["t"]
        ts = t.timestamp() + a.clock_offset
        src = "gps"
        lat, lon = m["lat"], m["lon"]
        if rel in overrides or p.name in overrides:
            lat, lon = overrides.get(rel) or overrides[p.name]
            src, m["acc"] = "override", None
        elif lat is None:
            hit = locate_on_tracks(ts, tracks, a.track_tol)
            if hit:
                lat, lon, src = round(hit[0], 6), round(hit[1], 6), "track"
                m["acc"] = round(max(10.0, hit[2] * 1.4), 1)
            else:
                problems.append((rel, "no GPS and no track within tolerance: add it to data/overrides.csv"))
                continue
        local = t.astimezone(tz)
        th = None
        if not a.no_thumbs:
            tp = ROOT / "thumbs" / (hashlib.md5(rel.encode()).hexdigest()[:10] + ".jpg")
            if thumb(p, tp, kind, m.get("dur")):
                th = tp.relative_to(ROOT).as_posix()
        media.append({
            "id": hashlib.md5(rel.encode()).hexdigest()[:8], "file": rel, "name": p.name, "type": kind,
            "thumb": th, "day": local.strftime("%Y-%m-%d"), "time": local.strftime("%H:%M:%S"),
            "h": round(local.hour + local.minute / 60 + local.second / 3600, 4), "ts": int(t.timestamp()),
            "lat": round(lat, 6), "lon": round(lon, 6), "acc": m["acc"], "src": src, "tsrc": m["tsrc"],
            "dur": m.get("dur"),
        })
        if i % 25 == 0:
            print(f"  {i}/{len(files)}")

    # sketches: data/sketches.csv  ->  image,photo,title,text   (lat/lon/date/time optional if photo is given)
    sketches = []
    sk = ROOT / "data" / "sketches.csv"
    if not sk.exists():
        print("sketches: data/sketches.csv not found (it must be named exactly that and sit inside the data folder)")
    else:
        norm = lambda n: re.sub(r"[^a-z0-9]", "", Path(n).stem.lower())   # IMG_7918.MOV == img7918 == IMG7918
        by_name = {x["name"].lower(): x for x in media}
        by_stem = {}
        for x in media:
            by_stem.setdefault(norm(x["name"]), x)
        with open(sk, newline="", encoding="utf-8-sig") as f:
            for row in csv.DictReader(f):
                img = (row.get("image") or "").strip()
                if not img or img.startswith("#"):
                    continue
                pn = (row.get("photo") or "").strip()
                ph = by_name.get(pn.lower()) or by_stem.get(norm(pn)) if pn else None
                if not (ROOT / "sketches" / img).exists():
                    print(f"  ! sketch image not found in sketches/: {img}")
                if pn and not ph:
                    print(f"  ! photo not found in media/: {pn}  (sketch: {img})")
                try:
                    lat = float(row["lat"]) if row.get("lat") else (ph["lat"] if ph else None)
                    lon = float(row["lon"]) if row.get("lon") else (ph["lon"] if ph else None)
                except ValueError:
                    lat = lon = None
                if lat is None:
                    problems.append((img, "sketch not placed: photo not found and no lat/lon given"))
                    continue
                sketches.append({"id": hashlib.md5(img.encode()).hexdigest()[:6], "image": "sketches/" + img,
                                 "title": (row.get("title") or img).strip(), "text": (row.get("text") or "").strip(),
                                 "date": (row.get("date") or "").strip() or (ph["day"] if ph else ""),
                                 "time": (row.get("time") or "").strip() or (ph["time"][:5] if ph else ""),
                                 "lat": lat, "lon": lon,
                                 "photo": ph["file"] if ph else None, "photoThumb": ph["thumb"] if ph else None})
        print(f"sketches placed: {len(sketches)}")

    days = sorted({x["day"] for x in media} | {t["day"] for t in tracks if t["day"]})
    day_defs = []
    for i, d in enumerate(days):
        dd = dt.date.fromisoformat(d)
        day_defs.append({"id": d, "label": dd.strftime("%a %-d %b") if sys.platform != "win32" else dd.strftime("%a %#d %b"),
                         "color": PALETTE[i % len(PALETTE)]})
    archive = {"generated": dt.datetime.now().isoformat(timespec="seconds"), "tz": a.tz, "days": day_defs,
               "media": media, "tracks": tracks, "sketches": sketches}
    (ROOT / "data" / "archive.js").write_text("window.ARCHIVE = " + json.dumps(archive, separators=(",", ":")) + ";\n", encoding="utf-8")

    notes = ROOT / "data" / "notes.js"
    if not notes.exists():
        notes.write_text(NOTES_TEMPLATE, encoding="utf-8")
        print("created data/notes.js (your places and sketches live here; it is never overwritten)")
    # report
    by_src = {}
    for x in media:
        by_src[x["src"]] = by_src.get(x["src"], 0) + 1
    print(f"\nplaced {len(media)} of {len(files)} files   ({', '.join(f'{k}: {v}' for k, v in by_src.items())})")
    for d in day_defs:
        print(f"  {d['label']}: {sum(1 for x in media if x['day'] == d['id'])} files")
    fb = [x["name"] for x in media if x["tsrc"] in ("creation_time-fallback", "assumed-tz")]
    if fb:
        print(f"\n{len(fb)} files had no timezone or capture-time tag, so times are assumed ({a.tz}); check: {', '.join(fb[:8])}{' ...' if len(fb) > 8 else ''}")
    if problems:
        print(f"\n{len(problems)} files NOT placed:")
        for rel, why in problems[:40]:
            print(f"  - {rel}: {why}")
        (ROOT / "data" / "unplaced.txt").write_text("\n".join(f"{r}\t{w}" for r, w in problems), encoding="utf-8")
    print("\nOpen index.html in your browser (it needs internet for the map tiles).")


def export_spots(a):
    """Copy media (and sketches) near the given points into export/<name>/ so they can be shared."""
    import shutil
    js = (ROOT / "data" / "archive.js").read_text(encoding="utf-8")
    arch = json.loads(js[js.index("{"):js.rindex("}") + 1])
    pts = [tuple(float(v) for v in sp.split(",")) for sp in a.export_spot]
    near = lambda x: any(metres(x["lat"], x["lon"], la, lo) <= a.radius for la, lo in pts)
    sel = [m for m in arch["media"] if near(m)]
    sks = [k for k in arch.get("sketches", []) if near(k)]
    if a.max_per_day:
        keep = []
        for d in sorted({m["day"] for m in sel}):
            day = sorted((m for m in sel if m["day"] == d), key=lambda m: m["ts"])
            n = a.max_per_day
            keep += day if len(day) <= n else [day[round(i * (len(day) - 1) / (n - 1))] for i in range(n)] if n > 1 else day[:1]
        sel = keep
    size = sum((ROOT / m["file"]).stat().st_size for m in sel if (ROOT / m["file"]).exists()) / 1e6
    print(f"{len(sel)} media items ({size:.0f} MB) and {len(sks)} sketches within {a.radius:g} m of {len(pts)} point(s)")
    for d in arch["days"]:
        print(f"  {d['label']}: {sum(1 for m in sel if m['day'] == d['id'])}")
    if a.dry_run:
        print("dry run: nothing copied. Remove --dry-run to copy.")
        return
    out = ROOT / "export" / a.name
    (out / "media").mkdir(parents=True, exist_ok=True)
    (out / "sketches").mkdir(exist_ok=True)
    for m in sel:
        src, dst = ROOT / m["file"], out / "media" / Path(m["file"]).name
        if a.small and m["type"] == "photo":
            with Image.open(src) as im:
                im = ImageOps.exif_transpose(im).convert("RGB")
                im.thumbnail((1280, 1280))
                im.save(dst.with_suffix(".jpg"), "JPEG", quality=85)
        elif a.small:
            r = subprocess.run(["ffmpeg", "-v", "error", "-y", "-i", str(src), "-map_metadata", "0",
                                "-vf", "scale=-2:540", "-c:v", "libx264", "-preset", "veryfast", "-crf", "28",
                                "-c:a", "aac", "-b:a", "64k", str(dst.with_suffix(".mp4"))], capture_output=True)
            if r.returncode != 0:
                print("  ! could not shrink", src.name, "- copying original")
                shutil.copy2(src, dst)
        else:
            shutil.copy2(src, dst)
    for k in sks:
        if (ROOT / k["image"]).exists():
            shutil.copy2(ROOT / k["image"], out / "sketches" / Path(k["image"]).name)
    with open(out / "sketches.csv", "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["image", "photo", "title", "text", "date", "time", "lat", "lon"])
        for k in sks:
            w.writerow([Path(k["image"]).name, Path(k["photo"] or "").name, k["title"], k["text"], k["date"], k["time"], k["lat"], k["lon"]])
    with open(out / "items.csv", "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(["file", "type", "day", "time", "lat", "lon", "gps_accuracy_m", "location_source"])
        for m in sel:
            w.writerow([Path(m["file"]).name, m["type"], m["day"], m["time"], m["lat"], m["lon"], m["acc"], m["src"]])
    if a.small:
        tot = sum(f.stat().st_size for f in (out / "media").iterdir()) / 1e6
        print(f"small copies total {tot:.0f} MB. (File names keep the same number; extension may change to .jpg/.mp4.)")
    print(f"copied to {out}\nNow zip that folder (right-click > Compress) and upload the zip here.")


NOTES_TEMPLATE = """// Your own places and sketches. This file is never overwritten by build_archive.py.
// Edit it by hand, then refresh index.html.

// Places worth naming, including sites you only visited once (e.g. a market).
// day is optional (a date such as "2026-09-10"). Right-click the map to copy coordinates.
window.PLACES = [
  // { name: "Example place", lat: -6.1630, lon: 39.1890, day: "2026-09-10", note: "What happened here" },
];

// Sketches: image is a path relative to this folder (put scans in a sketches/ folder).
window.SKETCHES = [
  // { id: "s1", title: "Shangani street", image: "sketches/s1.jpg", lat: -6.1628, lon: 39.1877,
  //   date: "2026-09-10", time: "14:10", text: "Short excerpt of the affect text" },
];
"""

if __name__ == "__main__":
    main()
