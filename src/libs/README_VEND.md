Vendor Three.js locally

To make the app work fully offline, download these files into `src/libs/`:

- `three.min.js` from https://cdn.jsdelivr.net/npm/three@0.152.2/build/three.min.js
- `OrbitControls.js` from https://cdn.jsdelivr.net/npm/three@0.152.2/examples/js/controls/OrbitControls.js

Place them at:

```
C:/Users/admin/Documents/AI/src/libs/three.min.js
C:/Users/admin/Documents/AI/src/libs/OrbitControls.js
```

Index.html is already set to prefer local files if present and will fall back to CDN if not.
