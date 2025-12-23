# JARVIS Orb — Audio Reactive UI

This is a minimal web UI that renders a 3D "orb" which reacts to live microphone audio using Three.js and the Web Audio API. It's intended as a visual frontend for a future virtual assistant.

Quick start

1. Serve the folder locally (browsers block `getUserMedia` on `file://`). From the project root run one of:

PowerShell (recommended):
```
# from project folder (C:\Users\admin\Documents\AI)
python -m http.server 8000
```

Or (if you have Node):
```
npx http-server -c-1 .
```

2. Open `http://localhost:8000` in your browser.
3. Click `Start Mic` and allow microphone access. Use the sensitivity slider to adjust responsiveness.

Notes
- This is a UI prototype: the shader uses simple trigonometric displacements for a stylized reactive effect.
- For production/advanced visuals consider adding Perlin/Simplex noise, frequency band mapping, post-processing, and texture/lighting improvements.

Files
- `index.html` — entry page with UI controls
- `styles.css` — minimal styling
- `src/main.js` — Three.js scene, shader, and audio code

Next steps I can implement for you
- Add Perlin noise-based displacement in GLSL
- Map bass/mid/treble frequency bands to different shader parameters
- Add recording or playback visualizations
