let scene, camera, renderer, orb, orbWire, uniforms, controls;
let analyser, dataArray, audioCtx, sourceNode;
let mediaStream, fallbackOsc, micMode = 'off';
let speechRecognition, recognitionActive = false, selectedVoice = null;
let lastTranscript = '', lastTranscriptAt = 0;
let wakeActive = false, wakeResetTimer = null;
let sessionActive = false;
let expectImmediateCommand = false;
let isSpeaking = false;
let micMutedForCommand = false;
let recognitionPausedForSpeech = false;
let lastCommandHandledAt = 0;
let lastCommandKey = '';
var speechRestartTimeout = null;
const customCommands = [];
const jokeBank = [
  'Why do JavaScript developers wear glasses? Because they do not C sharp.',
  'I told my computer I needed a break, and it said: no problem, I will go to sleep.',
  'There are 10 kinds of people in the world: those who understand binary and those who do not.',
  'Why did the developer go broke? Because he used up all his cache.',
  'My Wi-Fi went down for five minutes, so I had to talk to my family. They seem like nice people.',
  'I asked an AI to tell me a joke about modern technology, and it said: 404 humour not found.'
];
let amp = 0;
let signalBarEl, micStatusEl, brandStatusEl;
let ringOuterEl, ringInnerEl;
let voiceBars = [];
let listeningStatusEl;
let sleepScreenEl, sleepTimeEl, sleepDateEl;
let alarmIndicatorEl, alarmTimeDisplayEl;
let idleTimer = null;
let lastActivityTime = Date.now();
const IDLE_TIMEOUT = 10000; // 10 seconds
let timeAnnounceIntervalMinutes = 1; // default interval
let timeAnnounceTimerId = null;
let alarmTime = null; // { hours: number, minutes: number, timestamp: number }
let alarmSnoozeTime = null;
let alarmSound = null;
let alarmPlaying = false;
let alarmNotificationShown = false;
let alarmCheckInterval = null;
let onScreenKeyboardEl = null;
let activeInputEl = null;
let keyboardShiftActive = false;
let keyboardKeyClicked = false; // Flag to prevent hide when key is clicked

// Simple UI chimes to signal listening state / session changes.
// Approximate a small bell using a few short, decaying partials.
function playChime(freqBase = 880, freqTarget = 1320, duration = 0.12, volume = 0.28){
  try{
    const AudioCtx = window.AudioContext || window.webkitAudioContext;
    if (!AudioCtx) return;
    const ctx = new AudioCtx();
    const gain = ctx.createGain();
    gain.connect(ctx.destination);

    const now = ctx.currentTime;
    gain.gain.setValueAtTime(volume, now);
    gain.gain.exponentialRampToValueAtTime(0.001, now + duration + 0.18);

    // Fundamental
    const osc1 = ctx.createOscillator();
    osc1.type = 'sine';
    osc1.frequency.setValueAtTime(freqBase, now);
    osc1.connect(gain);
    osc1.start(now);

    // Slightly detuned overtone for "bell" shimmer
    const osc2 = ctx.createOscillator();
    osc2.type = 'sine';
    osc2.frequency.setValueAtTime(freqBase * 2.01, now);
    osc2.connect(gain);
    osc2.start(now + 0.005);

    // Higher, fast-decaying partial
    const osc3 = ctx.createOscillator();
    osc3.type = 'sine';
    osc3.frequency.setValueAtTime(freqTarget, now);
    const gain3 = ctx.createGain();
    gain3.gain.setValueAtTime(volume * 0.5, now);
    gain3.gain.exponentialRampToValueAtTime(0.001, now + duration);
    osc3.connect(gain3);
    gain3.connect(gain);
    osc3.start(now + 0.01);

    const stopTime = now + duration + 0.22;
    osc1.stop(stopTime);
    osc2.stop(stopTime);
    osc3.stop(stopTime);

    osc3.onended = () => ctx.close();
  }catch(e){
    console.warn('Chime playback failed:', e);
  }
}

function playStartChime(){
  // Brighter bell for start
  playChime(1100, 1800, 0.12, 0.32);
}

function playStopChime(){
  // Slightly lower bell for stop
  playChime(800, 1400, 0.12, 0.26);
}

// Simple in-memory cache for weather responses so repeated weather
// questions are instant, even on slow or flaky connections.
const weatherCache = new Map(); // key: normalized location, value: { data, fetchedAt }
const WEATHER_CACHE_TTL_MS = 10 * 60 * 1000; // 10 minutes

init();

async function init(){
  signalBarEl = document.getElementById('signalBar');
  micStatusEl = document.getElementById('micStatus');
  brandStatusEl = document.getElementById('brandStatus');
  ringOuterEl = document.querySelector('.ring-1');
  ringInnerEl = document.querySelector('.ring-2');
  listeningStatusEl = document.getElementById('listeningStatus');
  voiceBars = Array.from(document.querySelectorAll('.voice-bar'));
  sleepScreenEl = document.getElementById('sleepScreen');
  sleepTimeEl = document.getElementById('sleepTime');
  sleepDateEl = document.getElementById('sleepDate');
  alarmIndicatorEl = document.getElementById('alarmIndicator');
  alarmTimeDisplayEl = document.getElementById('alarmTimeDisplay');
  updateStatusText('Calibrating');
  setListening(false);
  updateAlarmIndicator();
  // Initialize alarm icon after sleep screen is set up
  setTimeout(() => {
    updateSleepAlarmIcon();
  }, 100);
  setupSpeechFeatures();
  setupCustomCommandsUI();
  setupOnScreenKeyboard();
  setupSleepScreen();
  setupAlarm();
  setupActivityTracking(); // Track mouse, keyboard, and other user activity
  resetIdleTimer();

  // Once core features are wired up, move out of "Calibrating" into an idle state
  updateStatusText('Idle');

  // Renderer
  renderer = new THREE.WebGLRenderer({antialias:true, alpha:true});
  renderer.setPixelRatio(window.devicePixelRatio);
  const container = document.getElementById('orbCanvas');
  const cw = Math.max(200, container.clientWidth);
  const ch = Math.max(200, container.clientHeight);
  renderer.setSize(cw, ch);
  container.appendChild(renderer.domElement);

  // Scene + Camera
  scene = new THREE.Scene();
  camera = new THREE.PerspectiveCamera(45, cw/ch, 0.1, 1000);
  camera.position.set(0,0,6);

  // Controls: try to use THREE.OrbitControls (global), otherwise dynamically import the module
  let ControlsClass = null;
  if (typeof THREE !== 'undefined' && THREE.OrbitControls) {
    ControlsClass = THREE.OrbitControls;
  } else if (window.OrbitControls) {
    ControlsClass = window.OrbitControls;
  } else {
    try{
      const mod = await import('https://unpkg.com/three@0.152.2/examples/jsm/controls/OrbitControls.js');
      ControlsClass = mod.OrbitControls;
      showDiag('Loaded OrbitControls module fallback');
    }catch(e){
      console.warn('Failed to load OrbitControls module:', e);
      showDiag('OrbitControls unavailable — continuing without orbit controls', true);
    }
  }
  if (ControlsClass){
    try{
      controls = new ControlsClass(camera, renderer.domElement);
      controls.enablePan = false;
      controls.enableZoom = true;
    }catch(e){
      console.warn('Failed to construct controls:', e);
      showDiag('Failed to initialize controls', true);
    }
  }

  // Light (subtle)
  scene.add(new THREE.AmbientLight(0xffffff, 0.2));
  const dir = new THREE.DirectionalLight(0xffffff, 0.6);
  dir.position.set(5,5,5);
  scene.add(dir);

  // Shader uniforms
  uniforms = {
    uTime: { value: 0 },
    uAmp: { value: 0 },
    uColor: { value: new THREE.Color(0x66ccff) },
    uResolution: { value: new THREE.Vector2(window.innerWidth, window.innerHeight) }
  };

  // Geometry + Materials
  const geo = new THREE.IcosahedronGeometry(1.6, 6);

  const mat = new THREE.ShaderMaterial({
    uniforms,
    vertexShader: vertexShader(),
    fragmentShader: fragmentShader(),
  });

  // Core shaded orb
  orb = new THREE.Mesh(geo, mat);
  scene.add(orb);

  // Wireframe shell for extra structure / interaction lines
  const wireGeo = new THREE.WireframeGeometry(geo);
  const wireMat = new THREE.LineBasicMaterial({
    color: 0x66ffe6,
    transparent: true,
    opacity: 0.4,
    linewidth: 1,
  });
  orbWire = new THREE.LineSegments(wireGeo, wireMat);
  scene.add(orbWire);

  // Create animated point-cloud ring overlay
  createPointRing();

  window.addEventListener('resize', onWindowResize);

  // UI hooks
  const startBtn = document.getElementById('startBtn');
  if (startBtn) {
    startBtn.addEventListener('click', handleMicButton);
  } else {
    console.warn('startBtn not found in DOM');
    showDiag('Start button not found', true);
  }
  setupSettingsPanel();

  // Attempt to keep microphone on automatically
  startMic();

  animate();
}

function animate(time){
  requestAnimationFrame(animate);
  const t = (time || 0) * 0.001;
  uniforms.uTime.value = t;

  // update point uniforms too
  if (pointsUniforms){
    pointsUniforms.uTime.value = t;
  }

  // Read audio amplitude and smooth it
  const rawAmp = getAudioAmplitude();
  const sensEl = document.getElementById('sensitivity');
  const sens = sensEl ? parseFloat(sensEl.value) : 1.0;

  // Use a slightly faster smoothing so motion tracks speech more tightly
  amp += (rawAmp * sens - amp) * 0.15;
  // Reset idle timer on significant mic activity
  if (amp > 0.1){
    resetIdleTimer();
  }
  let visualAmp = amp;

  // When Avril is speaking (TTS), drive the orb with a synthetic envelope
  // so it always moves in sync with her voice even if mic is muted.
  if (isSpeaking){
    const env = 0.5 + 0.5 * Math.sin(t * 3.2); // 3.2 Hz breathing pulse
    visualAmp = Math.max(visualAmp, env * 0.7);
  }

  visualAmp = Math.min(Math.max(visualAmp, 0), 1.0);

  uniforms.uAmp.value = visualAmp;
  if (pointsUniforms) pointsUniforms.uAmp.value = visualAmp;

  // Drive the circular UI rings from the same amplitude
  if (ringOuterEl && ringInnerEl){
    const outerScale = 1 + visualAmp * 0.25;
    const innerScale = 1 + visualAmp * 0.15;
    const glow = 40 + visualAmp * 140;
    ringOuterEl.style.transform = `translate(-50%,-50%) scale(${outerScale})`;
    ringOuterEl.style.boxShadow = `0 0 ${glow}px rgba(40,255,200,0.55)`;
    ringInnerEl.style.transform = `translate(-50%,-50%) scale(${innerScale}) rotate(${t * 40})`;
    ringInnerEl.style.opacity = String(0.4 + visualAmp * 0.6);
  }
  if (signalBarEl){
    const level = Math.min(100, 8 + amp * 92);
    signalBarEl.style.width = level + '%';
  }

  // Drive bottom visualizer bars (if present)
  if (voiceBars && voiceBars.length){
    voiceBars.forEach((el, i) => {
      const phase = (i / voiceBars.length) * Math.PI * 2;
      const pulsation = 0.75 + 0.25 * Math.sin(t * 4 + phase);
      const h = 0.2 + visualAmp * pulsation;
      el.style.transform = `scaleY(${h})`;
      el.style.opacity = String(0.25 + visualAmp * 0.7);
    });
  }

  // Rotate orb slightly based on amp
  if (orb){
    orb.rotation.y += 0.003 + visualAmp * 0.02;
  }
  if (orbWire){
    orbWire.rotation.y = orb.rotation.y;
    orbWire.rotation.x = 0.18 + visualAmp * 0.1;
    const wireScale = 1 + visualAmp * 0.1;
    orbWire.scale.set(wireScale, wireScale, wireScale);
  }

  if (controls && controls.update) controls.update();
  renderer.render(scene, camera);
}

// Point ring globals
let points, pointsUniforms;

function createPointRing(){
  const count = 2400;
  const positions = new Float32Array(count * 3);
  const colors = new Float32Array(count * 3);
  for(let i=0;i<count;i++){
    // distribute points on a sphere shell with slight randomness
    const u = Math.random();
    const v = Math.random();
    const theta = 2.0 * Math.PI * u;
    const phi = Math.acos(2.0 * v - 1.0);
    const r = 1.95 + (Math.random()-0.5) * 0.12; // slightly larger than orb
    const x = r * Math.sin(phi) * Math.cos(theta);
    const y = r * Math.sin(phi) * Math.sin(theta);
    const z = r * Math.cos(phi);
    positions[i*3+0] = x;
    positions[i*3+1] = y;
    positions[i*3+2] = z;
    const c = 0.6 + Math.random()*0.4;
    colors[i*3+0] = 0.2 * c;
    colors[i*3+1] = 1.0 * c;
    colors[i*3+2] = 0.9 * c;
  }

  const g = new THREE.BufferGeometry();
  g.setAttribute('position', new THREE.BufferAttribute(positions, 3));
  g.setAttribute('color', new THREE.BufferAttribute(colors, 3));

  pointsUniforms = {
    uTime: { value: 0 },
    uAmp: { value: 0 }
  };

  const pMat = new THREE.ShaderMaterial({
    uniforms: pointsUniforms,
    vertexShader: pointsVertexShader(),
    fragmentShader: pointsFragmentShader(),
    transparent: true,
    depthWrite: false,
    vertexColors: true
  });

  points = new THREE.Points(g, pMat);
  scene.add(points);
}

function onWindowResize(){
  const container = document.getElementById('orbCanvas');
  const cw = Math.max(200, container.clientWidth);
  const ch = Math.max(200, container.clientHeight);
  camera.aspect = cw / ch;
  camera.updateProjectionMatrix();
  renderer.setSize(cw, ch);
  uniforms.uResolution.value.set(cw, ch);
}

function startMic(){
  const diag = (m, err=false) => showDiag(m, err);
  if (micMode !== 'off') { diag('Microphone already active'); return; }
  const btn = document.getElementById('startBtn');
  if (btn){ setMicState('requesting'); btn.disabled = true; }
  if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia){
    diag('getUserMedia not available in this browser', true);
    // Graceful HUD hint instead of visible assistant bubble text
    updateStatusText('Voice mic unavailable in this browser');
    if (btn) btn.disabled = false;
    return;
  }
  navigator.mediaDevices.getUserMedia({
    audio: {
      echoCancellation: true,
      noiseSuppression: true,
      autoGainControl: true,
      channelCount: 1
    }
  }).then(stream => {
    audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    // resume context in case browser requires user gesture
    if (audioCtx.state === 'suspended') audioCtx.resume();
    sourceNode = audioCtx.createMediaStreamSource(stream);
    analyser = audioCtx.createAnalyser();
    analyser.fftSize = 2048;
    const bufferLength = analyser.frequencyBinCount;
    dataArray = new Uint8Array(bufferLength);
    sourceNode.connect(analyser);
    mediaStream = stream;
    micMode = 'stream';
    diag('Microphone streaming — OK');
    if (btn){ setMicState('on'); btn.disabled = false; }
    startSpeechRecognition();
  }).catch(err => {
    console.warn('Microphone access denied or error:', err);
    diag('Microphone denied or error — falling back to oscillator', true);
    // fallback: oscillator
    try{
      audioCtx = new (window.AudioContext || window.webkitAudioContext)();
      if (audioCtx.state === 'suspended') audioCtx.resume();
      const osc = audioCtx.createOscillator();
      osc.type = 'sine';
      osc.frequency.value = 220;
      analyser = audioCtx.createAnalyser();
      analyser.fftSize = 2048;
      dataArray = new Uint8Array(analyser.frequencyBinCount);
      osc.connect(analyser);
      // Don't connect to destination - keep it silent, only for visual effects
      // analyser.connect(audioCtx.destination); // Removed - no audio output
      osc.start();
      fallbackOsc = osc;
      micMode = 'fallback';
      stopSpeechRecognition();
      resetWakeState();
      // Hint user to tap mic / adjust permissions without assistant text bubble
      updateStatusText('Tap Mic to enable voice commands');
      if (btn){ setMicState('fallback'); btn.disabled = false; }
    }catch(e){
      console.error('Fallback oscillator failed:', e);
      diag('Audio initialization failed', true);
      if (btn){ setMicState('idle'); btn.disabled = false; }
    }
  }).finally(() => {
    const btnFinal = document.getElementById('startBtn');
    if (btnFinal) btnFinal.disabled = false;
  });
}

function stopMic(){
  const diag = (m, err=false) => showDiag(m, err);
  if (mediaStream){
    mediaStream.getTracks().forEach(track => track.stop());
    mediaStream = null;
  }
  if (sourceNode){
    try{ sourceNode.disconnect(); }catch(_e){}
    sourceNode = null;
  }
  if (fallbackOsc){
    try{ fallbackOsc.stop(); }catch(_e){}
    try{ fallbackOsc.disconnect(); }catch(_e){}
    fallbackOsc = null;
  }
  if (analyser){
    try{ analyser.disconnect && analyser.disconnect(); }catch(_e){}
    analyser = null;
  }
  dataArray = null;
  const ctx = audioCtx;
  audioCtx = null;
  if (ctx){
    ctx.close().catch(()=>{});
  }
  micMode = 'off';
  lastTranscript = '';
  lastTranscriptAt = 0;
  resetWakeState();
  const btn = document.getElementById('startBtn');
  if (btn) btn.disabled = false;
  setMicState('muted');
  stopSpeechRecognition();
  diag('Microphone stopped');
}

function handleMicButton(evt){
  if (evt) evt.preventDefault();
  resetIdleTimer(); // Reset idle timer on UI interaction
  if (micMode === 'off'){
    startMic();
  } else {
    stopMic();
  }
}

function setupSettingsPanel(){
  const settingsBtn = document.getElementById('settingsBtn');
  const settingsPanel = document.getElementById('settingsPanel');
  const closeSettingsBtn = document.getElementById('closeSettingsBtn');
  const timeIntervalSelect = document.getElementById('timeIntervalSelect');
  if (!settingsBtn || !settingsPanel) return;

  const openPanel = () => {
    settingsPanel.style.display = 'block';
    requestAnimationFrame(() => {
      settingsPanel.removeAttribute('hidden');
      settingsPanel.classList.add('showing');
      settingsBtn.setAttribute('aria-expanded','true');
    });
  };

  const closePanel = () => {
    if (!settingsPanel.hasAttribute('hidden')){
      settingsPanel.classList.remove('showing');
      settingsPanel.setAttribute('hidden','');
      settingsBtn.setAttribute('aria-expanded','false');
      // Hide keyboard when settings panel closes
      hideKeyboard();
      setTimeout(() => {
        if (settingsPanel.hasAttribute('hidden')) {
          settingsPanel.style.display = 'none';
        }
      }, 400);
    }
  };

  settingsBtn.addEventListener('click', (evt) => {
    evt.stopPropagation();
    resetIdleTimer(); // Reset idle timer on UI interaction
    if (settingsPanel.hasAttribute('hidden')) openPanel();
    else closePanel();
  });

  // Close button handler
  if (closeSettingsBtn) {
    closeSettingsBtn.addEventListener('click', (evt) => {
      evt.stopPropagation();
      resetIdleTimer(); // Reset idle timer on UI interaction
      closePanel();
    });
  }

  document.addEventListener('click', (evt) => {
    const target = evt.target;
    if (!settingsPanel.contains(target) && !settingsBtn.contains(target)) closePanel();
  });

  // Time announcement interval selector
  if (timeIntervalSelect){
    // Initialize from stored value (or default 1 minute)
    const stored = window.localStorage.getItem('avrilTimeIntervalMinutes');
    const initial = stored ? parseInt(stored, 10) : timeAnnounceIntervalMinutes;
    if (!Number.isNaN(initial) && ['1','5','10','15','30','60'].includes(String(initial))){
      timeAnnounceIntervalMinutes = initial;
    }
    timeIntervalSelect.value = String(timeAnnounceIntervalMinutes);
    updateTimeAnnounceSchedule();

    timeIntervalSelect.addEventListener('change', (evt) => {
      const value = parseInt(evt.target.value, 10);
      if (!value || Number.isNaN(value)) return;
      timeAnnounceIntervalMinutes = value;
      window.localStorage.setItem('avrilTimeIntervalMinutes', String(value));
      updateTimeAnnounceSchedule();
    });
  } else {
    // Ensure announcements still run with default even if settings UI missing
    updateTimeAnnounceSchedule();
  }

  // Store functions globally for voice commands
  window.openCommandList = openPanel;
  window.closeCommandList = closePanel;
}

function setupSpeechFeatures(){
  if ('speechSynthesis' in window){
    const assignVoice = () => {
      const voices = window.speechSynthesis.getVoices();
      if (!voices || !voices.length) return;
      const maleHints = /(male|daniel|brian|george|hugh)/i;
      selectedVoice =
        voices.find(v => v.lang === 'en-GB' && maleHints.test(v.name)) ||
        voices.find(v => v.lang === 'en-GB') ||
        voices.find(v => v.lang.startsWith('en'));
    };
    assignVoice();
    window.speechSynthesis.addEventListener('voiceschanged', assignVoice);
  }

  const Recognition = window.SpeechRecognition || window.webkitSpeechRecognition;
  if (!Recognition) {
    console.warn('SpeechRecognition unsupported in this browser');
    showResponse('Voice recognition unavailable in this browser.');
    return;
  }

  speechRecognition = new Recognition();
  speechRecognition.lang = 'en-GB';
  speechRecognition.continuous = true;
  speechRecognition.interimResults = false;
  speechRecognition.maxAlternatives = 1;
  speechRecognition.onresult = handleRecognitionResult;
  speechRecognition.onerror = handleRecognitionError;
  speechRecognition.onend = () => {
    recognitionActive = false;
    if (micMode !== 'off') {
      clearTimeout(speechRestartTimeout);
      speechRestartTimeout = setTimeout(() => startSpeechRecognition(), 700);
    }
  };
}

function startSpeechRecognition(){
  if (!speechRecognition || recognitionActive || micMode !== 'stream') return;
  try{
    speechRecognition.start();
    recognitionActive = true;
    // Chime to indicate we are actively listening
    playStartChime();
  }catch(err){
    if (err.name !== 'InvalidStateError'){
      console.warn('Speech recognition start failed:', err);
    }
  }
}

function setupOnScreenKeyboard(){
  onScreenKeyboardEl = document.getElementById('onScreenKeyboard');
  if (!onScreenKeyboardEl) {
    console.error('[Keyboard] Keyboard element not found!');
    return;
  }
  console.log('[Keyboard] Keyboard element found, setting up...');

  // Use event delegation on document to catch all input events (even in hidden panels)
  document.addEventListener('focus', (e) => {
    if (e.target.matches('input[type="text"], textarea')) {
      console.log('[Keyboard] Input focused:', e.target.id || e.target.name);
      activeInputEl = e.target;
      showKeyboard();
    }
  }, true); // Use capture phase

  document.addEventListener('click', (e) => {
    // Don't process if clicking on keyboard
    if (onScreenKeyboardEl && onScreenKeyboardEl.contains(e.target)) {
      console.log('[Keyboard] Click on keyboard detected in input handler, ignoring');
      return;
    }
    
    if (e.target.matches('input[type="text"], textarea')) {
      console.log('[Keyboard] Input clicked:', e.target.id || e.target.name);
      activeInputEl = e.target;
      showKeyboard();
    }
  }, true); // Use capture phase

  // Prevent default keyboard on mobile
  document.addEventListener('touchstart', (e) => {
    if (e.target.matches('input[type="text"], textarea')) {
      e.preventDefault();
      e.target.focus();
    }
  }, true);

  // Setup keyboard key handlers
  const keyboardKeys = onScreenKeyboardEl.querySelectorAll('.keyboard-key');
  keyboardKeys.forEach(key => {
    key.addEventListener('click', (e) => {
      keyboardKeyClicked = true; // Set flag
      e.preventDefault();
      e.stopPropagation(); // Prevent click from bubbling to document
      console.log('[Keyboard] Key clicked:', key.dataset.key);
      handleKeyboardKey(key.dataset.key);
      // Reset flag after a short delay
      setTimeout(() => {
        keyboardKeyClicked = false;
      }, 100);
    }, true); // Use capture phase - runs first
  });

  // Hide keyboard when clicking outside (but not on keyboard keys or inputs)
  document.addEventListener('click', (e) => {
    // Don't hide if a keyboard key was just clicked
    if (keyboardKeyClicked) {
      console.log('[Keyboard] Keyboard key was clicked, not hiding');
      return;
    }
    
    // Don't hide if clicking on keyboard or its children
    if (onScreenKeyboardEl && onScreenKeyboardEl.contains(e.target)) {
      console.log('[Keyboard] Click on keyboard, not hiding');
      return; // Click is on keyboard, don't hide
    }
    
    // Don't hide if clicking on an input
    if (e.target.matches('input[type="text"], textarea')) {
      console.log('[Keyboard] Click on input, not hiding');
      return; // Click is on input, don't hide
    }
    
    // Only hide if we have an active input
    if (activeInputEl) {
      console.log('[Keyboard] Click outside, hiding keyboard');
      hideKeyboard();
    }
  }, false); // Use bubble phase (runs after capture phase)

  // We intentionally do NOT hide the keyboard on blur, because clicking
  // the on-screen keys causes the input to blur. Instead we only hide
  // via the click-outside handler above or when Enter is pressed.
}

function showKeyboard(){
  if (!onScreenKeyboardEl) {
    console.error('[Keyboard] Keyboard element not found in showKeyboard');
    return;
  }
  console.log('[Keyboard] Showing keyboard');
  onScreenKeyboardEl.removeAttribute('hidden');
  // Force reflow to ensure the element is visible before animation
  onScreenKeyboardEl.offsetHeight;
  // Trigger animation
  requestAnimationFrame(() => {
    onScreenKeyboardEl.style.transform = 'translateY(0)';
  });
}

function hideKeyboard(){
  if (!onScreenKeyboardEl) return;
  console.log('[Keyboard] Hiding keyboard');
  onScreenKeyboardEl.style.transform = 'translateY(100%)';
  setTimeout(() => {
    if (onScreenKeyboardEl) {
      onScreenKeyboardEl.setAttribute('hidden', '');
    }
    activeInputEl = null;
    keyboardShiftActive = false;
    updateKeyboardCase();
  }, 300); // Match CSS transition duration
}

function handleKeyboardKey(key){
  if (!activeInputEl) return;

  const input = activeInputEl;
  
  // Ensure input stays focused
  if (document.activeElement !== input) {
    input.focus();
  }
  
  const start = input.selectionStart || 0;
  const end = input.selectionEnd || 0;
  const value = input.value;

  switch(key){
    case 'backspace':
      if (start > 0) {
        input.value = value.substring(0, start - 1) + value.substring(end);
        input.setSelectionRange(start - 1, start - 1);
      }
      break;
    case 'enter':
      if (input.tagName === 'TEXTAREA') {
        input.value = value.substring(0, start) + '\n' + value.substring(end);
        input.setSelectionRange(start + 1, start + 1);
      } else {
        hideKeyboard();
      }
      break;
    case 'shift':
      keyboardShiftActive = !keyboardShiftActive;
      updateKeyboardCase();
      break;
    case ' ':
      input.value = value.substring(0, start) + ' ' + value.substring(end);
      input.setSelectionRange(start + 1, start + 1);
      break;
    default:
      const char = keyboardShiftActive ? key.toUpperCase() : key.toLowerCase();
      input.value = value.substring(0, start) + char + value.substring(end);
      input.setSelectionRange(start + 1, start + 1);
      // Auto-disable shift after typing
      if (keyboardShiftActive && key.length === 1) {
        keyboardShiftActive = false;
        updateKeyboardCase();
      }
      break;
  }

  // Trigger input event for any listeners
  input.dispatchEvent(new Event('input', { bubbles: true }));
}

function updateKeyboardCase(){
  if (!onScreenKeyboardEl) return;
  const letterKeys = onScreenKeyboardEl.querySelectorAll('.keyboard-key[data-key]:not([data-key="shift"]):not([data-key="backspace"]):not([data-key="enter"]):not([data-key=" "])');
  letterKeys.forEach(key => {
    const keyValue = key.dataset.key;
    if (keyValue && keyValue.length === 1 && /[a-z]/.test(keyValue)) {
      key.textContent = keyboardShiftActive ? keyValue.toUpperCase() : keyValue.toLowerCase();
    }
  });
  
  // Update shift button appearance
  const shiftKey = onScreenKeyboardEl.querySelector('.keyboard-key[data-key="shift"]');
  if (shiftKey) {
    if (keyboardShiftActive) {
      shiftKey.style.background = 'rgba(123,255,224,0.3)';
      shiftKey.style.borderColor = 'rgba(123,255,224,0.5)';
    } else {
      shiftKey.style.background = '';
      shiftKey.style.borderColor = '';
    }
  }
}

function setupCustomCommandsUI(){
  const panel = document.getElementById('settingsPanel');
  if (!panel) return;
  const phraseInput = panel.querySelector('#customCommandPhrase');
  const responseInput = panel.querySelector('#customCommandResponse');
  const addBtn = panel.querySelector('#addCommandBtn');
  const listEl = panel.querySelector('.command-list-items');
  if (!phraseInput || !responseInput || !addBtn || !listEl) return;

  const staticCount = listEl.children.length; // built-in commands
  let editingIndex = null;

  loadCustomCommands();

  function renderCustomCommands(){
    // remove any existing custom items
    while (listEl.children.length > staticCount){
      listEl.removeChild(listEl.lastChild);
    }
    // re-add from customCommands
    customCommands.forEach((cmd, idx) => {
      const label = cmd.phrase || cmd.key || '';
      const li = document.createElement('li');
      const span = document.createElement('span');
      span.className = 'kw';
      span.textContent = label;
      li.appendChild(span);
      li.addEventListener('click', () => {
        phraseInput.value = label;
        responseInput.value = cmd.response;
        editingIndex = idx;
        addBtn.textContent = 'Update';
      });
      listEl.appendChild(li);
    });
  }

  renderCustomCommands();

  addBtn.addEventListener('click', () => {
    const phrase = (phraseInput.value || '').trim();
    const response = (responseInput.value || '').trim();
    if (!phrase || !response) {
      console.warn('Cannot add custom command without phrase and response');
      return;
    }
    const key = sanitizePhrase(phrase);
    if (!key){
      console.warn('Command phrase too short after sanitization');
      return;
    }

    if (editingIndex === null){
      customCommands.push({ key, phrase, response });
      console.log('[CustomCommand] Added', { key, phrase, response });
    } else {
      customCommands[editingIndex] = { key, phrase, response };
      console.log('[CustomCommand] Updated', { index: editingIndex, key, phrase, response });
    }

    saveCustomCommands();
    renderCustomCommands();
    phraseInput.value = '';
    responseInput.value = '';
    editingIndex = null;
    addBtn.textContent = 'Save';
  });
}

function setupSleepScreen(){
  if (!sleepScreenEl || !sleepTimeEl || !sleepDateEl) return;
  
  // Update clock every second
  setInterval(updateSleepClock, 1000);
  updateSleepClock();
  // Initialize alarm icon on setup
  updateSleepAlarmIcon();
}

function updateSleepAlarmIcon(){
  if (!sleepScreenEl) {
    console.log('[AlarmIcon] sleepScreenEl not found');
    return;
  }
  
  const sleepClock = sleepScreenEl.querySelector('.sleep-clock');
  if (!sleepClock) {
    console.log('[AlarmIcon] sleep-clock not found');
    return;
  }
  
  const activeAlarm = alarmSnoozeTime || alarmTime;
  let alarmIcon = sleepClock.querySelector('.alarm-icon');
  
  console.log('[AlarmIcon] activeAlarm:', activeAlarm, 'existing icon:', !!alarmIcon);
  
  if (activeAlarm && !alarmIcon){
    // Create alarm icon SVG
    alarmIcon = document.createElementNS('http://www.w3.org/2000/svg', 'svg');
    alarmIcon.setAttribute('class', 'alarm-icon');
    alarmIcon.setAttribute('width', '32');
    alarmIcon.setAttribute('height', '32');
    alarmIcon.setAttribute('viewBox', '0 0 24 24');
    alarmIcon.setAttribute('fill', 'none');
    alarmIcon.setAttribute('stroke', '#8bffe5');
    alarmIcon.setAttribute('stroke-width', '2');
    alarmIcon.setAttribute('stroke-linecap', 'round');
    alarmIcon.setAttribute('stroke-linejoin', 'round');
    
    // Alarm bell path
    const path = document.createElementNS('http://www.w3.org/2000/svg', 'path');
    path.setAttribute('d', 'M6 8a6 6 0 0 1 12 0c0 7 3 9 3 9H3s3-2 3-9');
    alarmIcon.appendChild(path);
    
    const path2 = document.createElementNS('http://www.w3.org/2000/svg', 'path');
    path2.setAttribute('d', 'M13.73 21a2 2 0 0 1-3.46 0');
    alarmIcon.appendChild(path2);
    
    // Insert before clock-time element for better positioning
    const clockTime = sleepClock.querySelector('.clock-time');
    if (clockTime) {
      clockTime.parentNode.insertBefore(alarmIcon, clockTime);
    } else {
      sleepClock.insertBefore(alarmIcon, sleepClock.firstChild);
    }
    console.log('[AlarmIcon] Icon created and inserted');
  } else if (!activeAlarm && alarmIcon){
    alarmIcon.remove();
    console.log('[AlarmIcon] Icon removed');
  }
}

function setupAlarm(){
  // Load saved alarm from localStorage
  loadAlarm();
  
  // Check alarm more frequently (every 100ms) for better accuracy
  alarmCheckInterval = setInterval(checkAlarm, 100);
  
  // Create alarm sound using Web Audio API
  createAlarmSound();
  
  console.log('Alarm system initialized');
}

function createAlarmSound(){
  // Create a simple beeping alarm sound using Web Audio API
  try {
    const audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    alarmSound = audioCtx;
  } catch(e) {
    console.warn('Could not create audio context for alarm:', e);
  }
}

let alarmBeepInterval = null;

async function playAlarmSound(){
  if (!alarmSound) {
    console.warn('Alarm sound context not available');
    return;
  }
  
  try {
    const audioCtx = alarmSound;
    
    // Resume AudioContext if suspended (browsers require user interaction)
    if (audioCtx.state === 'suspended') {
      await audioCtx.resume();
    }
    
    // Clear any existing interval
    if (alarmBeepInterval) {
      clearInterval(alarmBeepInterval);
      alarmBeepInterval = null;
    }
    
    // Play initial beep
    const playBeep = () => {
      if (!alarmPlaying) return;
      
      try {
        const oscillator = audioCtx.createOscillator();
        const gainNode = audioCtx.createGain();
        
        oscillator.connect(gainNode);
        gainNode.connect(audioCtx.destination);
        
        oscillator.frequency.value = 800;
        oscillator.type = 'sine';
        
        gainNode.gain.setValueAtTime(0.3, audioCtx.currentTime);
        gainNode.gain.exponentialRampToValueAtTime(0.01, audioCtx.currentTime + 0.5);
        
        oscillator.start(audioCtx.currentTime);
        oscillator.stop(audioCtx.currentTime + 0.5);
      } catch(e) {
        console.warn('Error playing beep:', e);
      }
    };
    
    playBeep();
    
    // Repeat the beep every 600ms
    alarmBeepInterval = setInterval(playBeep, 600);
    
    console.log('Alarm sound started');
  } catch(e) {
    console.warn('Could not play alarm sound:', e);
  }
}

function stopAlarmSound(){
  console.log('Stopping alarm sound');
  alarmPlaying = false;
  if (alarmBeepInterval) {
    clearInterval(alarmBeepInterval);
    alarmBeepInterval = null;
  }
  window.lastTriggeredAlarm = null;
}

function checkAlarm(){
  if (!alarmTime && !alarmSnoozeTime) return;
  
  const now = new Date();
  const currentHours = now.getHours();
  const currentMinutes = now.getMinutes();
  const currentSeconds = now.getSeconds();
  
  // Check if alarm should trigger
  const targetTime = alarmSnoozeTime || alarmTime;
  if (!targetTime) return;
  
  const targetHours = targetTime.hours;
  const targetMinutes = targetTime.minutes;
  
  // Calculate target time for today
  const targetTimeToday = new Date(now);
  targetTimeToday.setHours(targetHours, targetMinutes, 0, 0);
  
  // If target time has passed today, set it for tomorrow
  if (targetTimeToday.getTime() < now.getTime()) {
    targetTimeToday.setDate(targetTimeToday.getDate() + 1);
  }
  
  // Check if it's 5 minutes before alarm (for notification)
  const fiveMinutesBefore = new Date(targetTimeToday);
  fiveMinutesBefore.setMinutes(fiveMinutesBefore.getMinutes() - 5);
  
  const timeUntilAlarm = targetTimeToday.getTime() - now.getTime();
  const timeUntilNotification = fiveMinutesBefore.getTime() - now.getTime();
  
  // Check if we're within 5 minutes before alarm (notification)
  if (timeUntilNotification >= 0 && timeUntilNotification < 60000 && !alarmNotificationShown) {
    alarmNotificationShown = true;
    const timeStr = formatTime12Hour(targetHours, targetMinutes);
    speakResponse(`Alarm set for ${timeStr} will go off in 5 minutes.`);
  }
  
  // Check if alarm time has been reached (within 2 second window for reliability)
  // Check if current time matches alarm time (with 2 second tolerance)
  const timeMatch = currentHours === targetHours && 
                    currentMinutes === targetMinutes && 
                    currentSeconds >= 0 && 
                    currentSeconds < 2;
  
  if (timeMatch || (timeUntilAlarm >= -2000 && timeUntilAlarm < 2000)) {
    // Only trigger once per alarm time
    const alarmKey = `${targetHours}:${targetMinutes}:${now.getDate()}`;
    if (!window.lastTriggeredAlarm || window.lastTriggeredAlarm !== alarmKey) {
      console.log(`Alarm triggered at ${currentHours}:${currentMinutes}:${currentSeconds}`);
      window.lastTriggeredAlarm = alarmKey;
      triggerAlarm();
      // Reset after 10 seconds to allow re-triggering if needed
      setTimeout(() => {
        if (window.lastTriggeredAlarm === alarmKey) {
          window.lastTriggeredAlarm = null;
        }
      }, 10000);
    }
  }
}

async function triggerAlarm(){
  if (alarmPlaying) {
    console.log('Alarm already playing, skipping trigger');
    return;
  }
  
  console.log('Triggering alarm...');
  alarmPlaying = true;
  await playAlarmSound();
  
  // Greet user after a short delay
  setTimeout(async () => {
    const nowDate = new Date();
    const timeStr = nowDate.toLocaleTimeString('en-US', { hour: 'numeric', minute: '2-digit', hour12: true });
    
    // Get weather - try to use a default location or get from user's location.
    // Use cache + short timeout so this never stalls the greeting.
    let weatherMsg = '';
    const defaultLocation = 'London';
    const cacheKey = defaultLocation.toLowerCase();
    const nowMs = Date.now();
    const cached = weatherCache.get(cacheKey);

    if (cached && (nowMs - cached.fetchedAt) < WEATHER_CACHE_TTL_MS) {
      const current = cached.data;
      const desc = current.weatherDesc && current.weatherDesc[0] ? current.weatherDesc[0].value : 'unknown conditions';
      const temp = current.temp_C;
      weatherMsg = ` The weather in ${defaultLocation} is ${desc.toLowerCase()} at ${temp} degrees Celsius.`;
    } else if (navigator.onLine) {
      try {
        const controller = new AbortController();
        const timeoutId = setTimeout(() => controller.abort(), 3000); // 3 second timeout
        const response = await fetch(`https://wttr.in/${encodeURIComponent(defaultLocation)}?format=j1`, {
          signal: controller.signal
        });
        clearTimeout(timeoutId);
        if (response.ok) {
          const data = await response.json();
          const current = data && data.current_condition && data.current_condition[0];
          if (current) {
            weatherCache.set(cacheKey, { data: current, fetchedAt: nowMs });
            const desc = current.weatherDesc && current.weatherDesc[0] ? current.weatherDesc[0].value : 'unknown conditions';
            const temp = current.temp_C;
            weatherMsg = ` The weather in ${defaultLocation} is ${desc.toLowerCase()} at ${temp} degrees Celsius.`;
          }
        }
      } catch(e) {
        console.warn('Could not fetch weather for alarm greeting:', e);
        weatherMsg = ' The weather is pleasant today.';
      }
    } else {
      weatherMsg = ' The weather is pleasant today.';
    }
    
    speakResponse(`Good morning. It is ${timeStr}.${weatherMsg}`);
  }, 2000);
}

function formatTime12Hour(hours, minutes){
  const hours12 = hours === 0 ? 12 : hours > 12 ? hours - 12 : hours;
  const ampm = hours >= 12 ? 'PM' : 'AM';
  return `${String(hours12).padStart(2, '0')}:${String(minutes).padStart(2, '0')} ${ampm}`;
}

function parseAlarmTime(text){
  // Try to parse time from text like "set alarm for 7:30 AM" or "alarm at 7 30"
  const timePatterns = [
    /(\d{1,2}):(\d{2})\s*(am|pm|AM|PM)/i,
    /(\d{1,2})\s+(\d{2})\s*(am|pm|AM|PM)/i,
    /(\d{1,2}):(\d{2})/,
    /(\d{1,2})\s+(\d{2})/,
    /(\d{1,2})\s*(am|pm|AM|PM)/i,
  ];
  
  for (const pattern of timePatterns) {
    const match = text.match(pattern);
    if (match) {
      let hours = parseInt(match[1], 10);
      let minutes = match[2] ? parseInt(match[2], 10) : 0;
      const ampm = match[3] ? match[3].toUpperCase() : null;
      
      // Handle AM/PM
      if (ampm === 'PM' && hours !== 12) {
        hours += 12;
      } else if (ampm === 'AM' && hours === 12) {
        hours = 0;
      }
      
      // If no AM/PM specified, assume 24-hour format or use current context
      if (!ampm && hours < 12) {
        // Could be AM, but we'll assume user means morning if hours < 12
      }
      
      if (hours >= 0 && hours < 24 && minutes >= 0 && minutes < 60) {
        return { hours, minutes };
      }
    }
  }
  
  return null;
}

function saveAlarm(){
  try {
    const data = alarmTime ? JSON.stringify(alarmTime) : null;
    if (data) {
      window.localStorage.setItem('avrilAlarm', data);
    } else {
      window.localStorage.removeItem('avrilAlarm');
    }
  } catch(e) {
    console.warn('Failed to save alarm:', e);
  }
}

function loadAlarm(){
  try {
    const raw = window.localStorage.getItem('avrilAlarm');
    if (raw) {
      const parsed = JSON.parse(raw);
      if (parsed && typeof parsed.hours === 'number' && typeof parsed.minutes === 'number') {
        alarmTime = parsed;
        updateAlarmIndicator();
        updateSleepAlarmIcon();
      }
    }
  } catch(e) {
    console.warn('Failed to load alarm:', e);
  }
}

function setAlarm(hours, minutes){
  alarmTime = { hours, minutes };
  alarmSnoozeTime = null;
  alarmNotificationShown = false;
  saveAlarm();
  updateAlarmIndicator();
  updateSleepAlarmIcon();
}

function cancelAlarm(){
  alarmTime = null;
  alarmSnoozeTime = null;
  alarmNotificationShown = false;
  stopAlarm();
  saveAlarm();
  updateAlarmIndicator();
  updateSleepAlarmIcon();
}

function updateAlarmIndicator(){
  if (!alarmIndicatorEl || !alarmTimeDisplayEl) return;
  
  const activeAlarm = alarmSnoozeTime || alarmTime;
  const viewport = document.querySelector('.viewport');
  
  if (activeAlarm){
    const timeStr = formatTime12Hour(activeAlarm.hours, activeAlarm.minutes);
    alarmTimeDisplayEl.textContent = timeStr;
    
    // Fade in animation
    alarmIndicatorEl.style.display = 'block';
    requestAnimationFrame(() => {
      alarmIndicatorEl.removeAttribute('hidden');
    });
    
    // Expand viewport when alarm indicator appears with animation
    if (viewport) {
      viewport.style.width = '520px';
    }
  } else {
    // Fade out animation
    alarmIndicatorEl.setAttribute('hidden', '');
    setTimeout(() => {
      if (alarmIndicatorEl.hasAttribute('hidden')) {
        alarmIndicatorEl.style.display = 'none';
      }
    }, 500);
    
    // Contract viewport when alarm indicator is hidden
    if (viewport) {
      viewport.style.width = '480px';
    }
  }
  
  // Update sleep screen alarm icon
  updateSleepAlarmIcon();
}

function stopAlarm(){
  stopAlarmSound();
  alarmPlaying = false;
  alarmSnoozeTime = null;
  // Optionally clear the alarm completely
  // alarmTime = null;
  // saveAlarm();
}

function snoozeAlarm(){
  stopAlarmSound();
  alarmPlaying = false;
  
  const now = new Date();
  const snoozeTime = new Date(now);
  snoozeTime.setMinutes(snoozeTime.getMinutes() + 5);
  
  alarmSnoozeTime = {
    hours: snoozeTime.getHours(),
    minutes: snoozeTime.getMinutes()
  };
  alarmNotificationShown = false;
  updateAlarmIndicator();
  updateSleepAlarmIcon();
}

function updateSleepClock(){
  if (!sleepTimeEl || !sleepDateEl) return;
  const now = new Date();
  const hours = now.getHours();
  const minutes = now.getMinutes();
  const seconds = now.getSeconds();
  
  // Convert to 12-hour format
  const hours12 = hours === 0 ? 12 : hours > 12 ? hours - 12 : hours;
  const ampm = hours >= 12 ? 'PM' : 'AM';
  
  const timeStr = `${String(hours12).padStart(2, '0')}:${String(minutes).padStart(2, '0')}:${String(seconds).padStart(2, '0')} ${ampm}`;
  const dateStr = now.toLocaleDateString('en-GB', { weekday: 'long', day: 'numeric', month: 'long' });
  
  sleepTimeEl.textContent = timeStr;
  sleepDateEl.textContent = dateStr;
  
  // Update alarm icon
  updateSleepAlarmIcon();
}

function showSleepScreen(){
  if (!sleepScreenEl) return;
  // Force reflow to ensure transition works
  sleepScreenEl.style.display = 'flex';
  sleepScreenEl.style.visibility = 'visible';
  requestAnimationFrame(() => {
    sleepScreenEl.removeAttribute('hidden');
    updateSleepClock();
    // Update alarm icon when sleep screen is shown
    updateSleepAlarmIcon();
  });
}

function hideSleepScreen(){
  if (!sleepScreenEl) return;
  sleepScreenEl.setAttribute('hidden', '');
  // After transition, hide completely
  setTimeout(() => {
    if (sleepScreenEl.hasAttribute('hidden')) {
      sleepScreenEl.style.display = 'none';
      sleepScreenEl.style.visibility = 'hidden';
    }
  }, 800);
}

function resetIdleTimer(){
  lastActivityTime = Date.now();
  hideSleepScreen();
  clearTimeout(idleTimer);
  idleTimer = setTimeout(() => {
    // Double-check that there's been no activity since the timer started
    const timeSinceLastActivity = Date.now() - lastActivityTime;
    if (timeSinceLastActivity >= IDLE_TIMEOUT) {
      showSleepScreen();
    }
  }, IDLE_TIMEOUT);
}

function setupActivityTracking(){
  // Track mouse movement
  let mouseMoveThrottle = null;
  document.addEventListener('mousemove', () => {
    if (mouseMoveThrottle) return;
    mouseMoveThrottle = setTimeout(() => {
      resetIdleTimer();
      mouseMoveThrottle = null;
    }, 100); // Throttle to once per 100ms
  }, { passive: true });
  
  // Track mouse clicks
  document.addEventListener('click', () => {
    resetIdleTimer();
  }, { passive: true });
  
  // Track keyboard input (typing)
  document.addEventListener('keydown', () => {
    resetIdleTimer();
  }, { passive: true });
  
  // Track keyboard key presses (on-screen keyboard)
  document.addEventListener('keyup', () => {
    resetIdleTimer();
  }, { passive: true });
  
  // Track touch events (for mobile)
  document.addEventListener('touchstart', () => {
    resetIdleTimer();
  }, { passive: true });
  
  document.addEventListener('touchmove', () => {
    resetIdleTimer();
  }, { passive: true });
  
  // Track scroll events
  let scrollThrottle = null;
  document.addEventListener('scroll', () => {
    if (scrollThrottle) return;
    scrollThrottle = setTimeout(() => {
      resetIdleTimer();
      scrollThrottle = null;
    }, 200); // Throttle to once per 200ms
  }, { passive: true });
  
  // Track input field focus/typing
  document.addEventListener('input', () => {
    resetIdleTimer();
  }, { passive: true });
  
  document.addEventListener('focus', () => {
    resetIdleTimer();
  }, true); // Use capture phase
  
  // Track any pointer events (mouse, touch, pen)
  document.addEventListener('pointermove', () => {
    resetIdleTimer();
  }, { passive: true });
}

function updateTimeAnnounceSchedule(){
  if (timeAnnounceTimerId){
    clearInterval(timeAnnounceTimerId);
    timeAnnounceTimerId = null;
  }
  const mins = timeAnnounceIntervalMinutes;
  if (!mins || mins <= 0) return;
  const intervalMs = mins * 60 * 1000;
  timeAnnounceTimerId = setInterval(announceCurrentTime, intervalMs);
}

function announceCurrentTime(){
  try{
    const now = new Date();
    const timeStr = now.toLocaleTimeString('en-US', {
      hour: 'numeric',
      minute: '2-digit',
      hour12: true
    });
    speakResponse(`The time is ${timeStr}.`);
  }catch(e){
    console.warn('Failed to announce time:', e);
  }
}

function stopSpeechRecognition(){
  if (!speechRecognition) return;
  try{
    speechRecognition.stop();
  }catch(_e){}
  recognitionActive = false;
  clearTimeout(speechRestartTimeout);
  // Chime when listening session ends (e.g., mic muted or app put to sleep)
  playStopChime();
}

function handleRecognitionResult(evt){
  if (!evt.results || !evt.results.length) return;
  const index = typeof evt.resultIndex === 'number' ? evt.resultIndex : evt.results.length - 1;
  const result = evt.results[index];
  if (!result || !result.isFinal || !result[0]) return;
  const transcript = (result[0].transcript || '').trim();
  if (!transcript) return;
  const normalized = transcript.toLowerCase();
  const now = Date.now();
  if (normalized === lastTranscript && now - lastTranscriptAt < 1500){
    return;
  }
  lastTranscript = normalized;
  lastTranscriptAt = now;
  resetIdleTimer(); // Reset idle timer on voice activity
  
  processVoiceCommand(transcript).catch(err => {
    console.warn('Voice command handling failed:', err);
  });
}

function handleRecognitionError(evt){
  recognitionActive = false;
  const err = evt && evt.error ? evt.error : 'unknown';
  console.warn('Speech recognition error:', err);
  if (micMode !== 'off'){
    // Auto‑recovery for transient errors
    const recoverable = (
      err === 'no-speech' ||
      err === 'audio-capture' ||
      err === 'network' ||
      err === 'aborted'
    );
    if (recoverable){
      clearTimeout(speechRestartTimeout);
      speechRestartTimeout = setTimeout(() => startSpeechRecognition(), 1000);
    }
  }
}

async function processVoiceCommand(raw){
  const text = raw.toLowerCase().trim();
  if (!text) return;

  // Reset idle timer on any voice command processing
  resetIdleTimer();

  const keyText = sanitizePhrase(text);
  
  // Alarm commands work even when alarm is playing or without wake-up
  if (keyText.includes('stop alarm') || keyText.includes('stop the alarm')){
    stopAlarm();
    deliverResponse(raw, 'Alarm stopped.');
    lastCommandHandledAt = Date.now();
    lastCommandKey = keyText;
    return;
  }

  if (keyText.includes('cancel alarm') || keyText.includes('delete alarm') || keyText.includes('clear alarm')){
    cancelAlarm();
    deliverResponse(raw, 'Alarm cancelled.');
    lastCommandHandledAt = Date.now();
    lastCommandKey = keyText;
    return;
  }

  if (keyText.includes('snooze') || keyText.includes('snooze alarm')){
    snoozeAlarm();
    deliverResponse(raw, 'Alarm snoozed for 5 minutes.');
    lastCommandHandledAt = Date.now();
    lastCommandKey = keyText;
    return;
  }

  // If Avril is currently speaking, ignore any new transcripts to avoid
  // interpreting echo or partial phrases as fresh commands.
  if (isSpeaking){
    console.log('[Voice] Ignoring command while speaking:', text);
    return;
  }

  if (keyText === 'mute' || keyText.includes('mute mic') || keyText.includes('mute microphone')){
    if (speechRecognition && recognitionActive){
      stopSpeechRecognition();
      micMutedForCommand = true;
    }
    deliverResponse(raw, 'Muting my microphone while I respond.');
    lastCommandHandledAt = Date.now();
    lastCommandKey = keyText;
    return;
  }

  if (expectImmediateCommand){
    setListening(true);
    await handleCommandText(raw, text);
    return;
  }

  if (!sessionActive){
    if (isWakePhrase(text)){
      await acknowledgeWake(raw);
    } else {
      console.log('[Wake] Ignored phrase without wake word.');
    }
    return;
  }

  setListening(true);
  await handleCommandText(raw, text);
}

async function respondWithWeather(location, heard){
  const displayLocation = location.split(' ').map(word => {
    return word ? word[0].toUpperCase() + word.slice(1) : '';
  }).join(' ');

  const cacheKey = location.trim().toLowerCase();
  const now = Date.now();
  const cached = weatherCache.get(cacheKey);

  // Serve from cache if recent enough
  if (cached && (now - cached.fetchedAt) < WEATHER_CACHE_TTL_MS) {
    const current = cached.data;
    const desc = current.weatherDesc && current.weatherDesc[0] ? current.weatherDesc[0].value : 'unknown conditions';
    const temp = current.temp_C;
    const feels = current.FeelsLikeC || temp;
    const humidity = current.humidity;
    const responseText = `Weather in ${displayLocation} is ${desc.toLowerCase()} at ${temp} degrees Celsius, feeling like ${feels}, humidity ${humidity} percent.`;
    deliverResponse(heard, responseText);
    return;
  }

  // Check if offline
  if (!navigator.onLine) {
    deliverResponse(heard, `I'm offline and can't fetch weather data. Please check your internet connection.`);
    return;
  }

  showResponse(`Checking weather for ${displayLocation}…`, heard, false); // Short message, no subtitle
  try{
    const controller = new AbortController();
    const timeoutId = setTimeout(() => controller.abort(), 4000); // 4 second timeout for snappier failures
    const response = await fetch(`https://wttr.in/${encodeURIComponent(location)}?format=j1`, {
      signal: controller.signal
    });
    clearTimeout(timeoutId);
    if (!response.ok) throw new Error(`Weather request failed: ${response.status}`);
    const data = await response.json();
    const current = data && data.current_condition && data.current_condition[0];
    if (!current) throw new Error('No current weather data.');

    // Save to cache
    weatherCache.set(cacheKey, { data: current, fetchedAt: now });

    const desc = current.weatherDesc && current.weatherDesc[0] ? current.weatherDesc[0].value : 'unknown conditions';
    const temp = current.temp_C;
    const feels = current.FeelsLikeC || temp;
    const humidity = current.humidity;
    const responseText = `Weather in ${displayLocation} is ${desc.toLowerCase()} at ${temp} degrees Celsius, feeling like ${feels}, humidity ${humidity} percent.`;
    deliverResponse(heard, responseText);
  }catch(err){
    console.warn('Weather lookup failed:', err);
    if (err.name === 'AbortError') {
      deliverResponse(heard, `Weather request timed out. I'm having trouble connecting to the weather service.`);
    } else if (!navigator.onLine) {
      deliverResponse(heard, `I'm offline and can't fetch weather data. Please check your internet connection.`);
    } else {
      deliverResponse(heard, `I couldn't fetch the weather for ${displayLocation} just now.`);
    }
  }
}

function deliverResponse(heard, responseText){
  // Use subtitle effect for longer responses (more than 50 chars)
  const useSubtitle = responseText.length > 50;
  showResponse(responseText, heard, useSubtitle);
  speakResponse(responseText);
}

function setListening(active){
  if (!listeningStatusEl) return;
  listeningStatusEl.textContent = active ? 'Listening…' : '';
}

function sanitizePhrase(str){
  return (str || '')
    .toLowerCase()
    .replace(/[^a-z0-9\s]/g,' ')
    .replace(/\s+/g,' ')
    .trim();
}

async function handleCommandText(raw, text){
  const original = (text || '');
  const trimmed = original.toLowerCase().trim();
  if (!trimmed) return;

  const keyText = sanitizePhrase(trimmed);
  if (!keyText) return;

  // If this is just another instance of the wake phrase, ignore it.
  // This avoids treating repeated "hello" / "wake up" as an unknown command.
  if (isWakePhrase(original)){
    console.log('[Commands] Ignoring wake phrase inside command handler:', original);
    return;
  }

  // Also ignore Avril's own prompt line "What is your command?"
  if (keyText === 'what is your command'){
    console.log('[Commands] Ignoring own prompt text:', original);
    return;
  }

  const wordCount = keyText.split(' ').filter(Boolean).length;

  // Conversation helper: user says "I have a question" to signal a new query
  if (keyText.startsWith('i have a question')){
    deliverResponse(raw, 'What is your question?');
    return;
  }

  // Alarm commands
  if (keyText.includes('stop alarm') || keyText.includes('stop the alarm')){
    stopAlarm();
    deliverResponse(raw, 'Alarm stopped.');
    lastCommandHandledAt = Date.now();
    lastCommandKey = keyText;
    resetWakeState();
    return;
  }

  if (keyText.includes('cancel alarm') || keyText.includes('delete alarm') || keyText.includes('clear alarm')){
    cancelAlarm();
    deliverResponse(raw, 'Alarm cancelled.');
    lastCommandHandledAt = Date.now();
    lastCommandKey = keyText;
    resetWakeState();
    return;
  }

  if (keyText.includes('snooze') || keyText.includes('snooze alarm')){
    snoozeAlarm();
    deliverResponse(raw, 'Alarm snoozed for 5 minutes.');
    lastCommandHandledAt = Date.now();
    lastCommandKey = keyText;
    resetWakeState();
    return;
  }

  // Set alarm command
  const alarmMatch = keyText.match(/(?:set|create|add)\s+(?:alarm|an alarm)\s+(?:for|at|to)?\s*(.+)/);
  if (alarmMatch && alarmMatch[1]){
    const timeStr = alarmMatch[1].trim();
    const parsedTime = parseAlarmTime(timeStr);
    if (parsedTime){
      setAlarm(parsedTime.hours, parsedTime.minutes);
      const formattedTime = formatTime12Hour(parsedTime.hours, parsedTime.minutes);
      deliverResponse(raw, `Alarm set for ${formattedTime}.`);
      lastCommandHandledAt = Date.now();
      lastCommandKey = keyText;
      resetWakeState();
      return;
    } else {
      deliverResponse(raw, 'I could not understand that time. Please say something like "set alarm for 7:30 AM".');
      lastCommandHandledAt = Date.now();
      lastCommandKey = keyText;
      resetWakeState();
      return;
    }
  }

  if (keyText.includes('tell me a joke') || keyText === 'joke' || keyText.includes('another joke')){
    const joke = jokeBank[Math.floor(Math.random() * jokeBank.length)];
    deliverResponse(raw, joke);
    lastCommandHandledAt = Date.now();
    lastCommandKey = keyText;
    resetWakeState();
    return;
  }

  if (keyText.includes('show commands') || keyText.includes('show command list') || keyText.includes('open commands')){
    if (window.openCommandList) {
      window.openCommandList();
      deliverResponse(raw, 'Command list opened.');
    } else {
      deliverResponse(raw, 'Command list is available in the settings panel.');
    }
    lastCommandHandledAt = Date.now();
    lastCommandKey = keyText;
    resetWakeState();
    return;
  }

  if (keyText.includes('close command list') || keyText.includes('close commands') || keyText.includes('hide command list')){
    if (window.closeCommandList) {
      window.closeCommandList();
      deliverResponse(raw, 'Command list closed.');
    }
    lastCommandHandledAt = Date.now();
    lastCommandKey = keyText;
    resetWakeState();
    return;
  }

  if (keyText.includes('command list') || keyText.includes('list of commands')){
    const message = 'Here are your commands: say "Hello" to wake me, then you can ask "What time is it?", "What is the date today?", "What is the weather in" followed by a city, "Set alarm for" followed by a time like "7:30 AM", "Stop alarm" to stop the alarm, "Cancel alarm" to delete the alarm, "Snooze" to snooze the alarm for 5 minutes, "Show commands" to open the command list, "Close command list" to close it, or use any custom command you have saved.';
    deliverResponse(raw, message);
    lastCommandHandledAt = Date.now();
    lastCommandKey = keyText;
    resetWakeState();
    return;
  }

  if (customCommands.length){
    const match = customCommands.find(cmd => keyText.includes(cmd.key));
    if (match){
      deliverResponse(raw, match.response);
      lastCommandHandledAt = Date.now();
      lastCommandKey = keyText;
      resetWakeState();
      return;
    }
  }

  if (
    keyText.includes('what time is it') ||
    keyText.includes('whats the time') ||
    keyText.includes('current time')
  ){
    const now = new Date();
    const timeStr = now.toLocaleTimeString('en-US', { hour: 'numeric', minute: '2-digit', hour12: true });
    deliverResponse(raw, `It is ${timeStr}.`);
    lastCommandHandledAt = Date.now();
    lastCommandKey = keyText;
    resetWakeState();
    return;
  }

  if (
    keyText.includes('what is the date') ||
    keyText.includes('whats the date') ||
    keyText.includes('date today') ||
    keyText.includes('todays date')
  ){
    const now = new Date();
    const dateStr = now.toLocaleDateString('en-GB', { weekday:'long', day:'numeric', month:'long', year:'numeric' });
    deliverResponse(raw, `Today is ${dateStr}.`);
    lastCommandHandledAt = Date.now();
    lastCommandKey = keyText;
    resetWakeState();
    return;
  }

  const weatherMatch = keyText.match(/weather(?:\s+(?:in|for))?\s+(.+)/);
  if (weatherMatch && weatherMatch[1]){
    const location = weatherMatch[1].trim();
    if (location){
      await respondWithWeather(location, raw);
      lastCommandHandledAt = Date.now();
      lastCommandKey = keyText;
      resetWakeState();
      return;
    }
  }

  // treat very short/noisy phrases as background and ignore
  if (wordCount < 2){
    console.log('[Commands] Ignoring short/noisy phrase:', keyText);
    return;
  }
  deliverResponse(raw, `I can't understand that command.`);
  resetWakeState();
}

function saveCustomCommands(){
  try{
    const data = JSON.stringify(customCommands);
    window.localStorage.setItem('avrilCustomCommands', data);
  }catch(e){
    console.warn('Failed to save custom commands:', e);
  }
}

function loadCustomCommands(){
  try{
    const raw = window.localStorage.getItem('avrilCustomCommands');
    if (!raw) return;
    const parsed = JSON.parse(raw);
    if (Array.isArray(parsed)){
      customCommands.length = 0;
      for (const item of parsed){
        if (item && typeof item.response === 'string'){
          const phrase = typeof item.phrase === 'string' ? item.phrase : '';
          const key = item.key ? sanitizePhrase(item.key) : sanitizePhrase(phrase);
          if (!key) continue;
          customCommands.push({ key, phrase, response: item.response });
        }
      }
    }
  }catch(e){
    console.warn('Failed to load custom commands:', e);
  }
}

function isWakePhrase(text){
  if (!text) return false;
  const sanitized = text
    .toLowerCase()
    .replace(/[^a-z\s]/g,' ')
    .replace(/\s+/g,' ')
    .trim();
  if (!sanitized) return false;
  // Accept "hello", "hello ...", "hey avril ..." and also legacy "wake up"
  if (sanitized === 'hello') return true;
  if (sanitized.startsWith('hello ')) return true;
  if (sanitized.includes(' hello ')) return true;
  if (sanitized === 'hey avril') return true;
  if (sanitized.startsWith('hey avril ')) return true;
  if (sanitized.includes(' hey avril ')) return true;
  if (sanitized.includes('wake up') || sanitized === 'wake up') return true;
  return false;
}

// Simple diag message helper: writes to #diag and console
function showDiag(msg, isError=false){
  const el = document.getElementById('diag');
  if (el){
    const d = document.createElement('div');
    d.textContent = msg;
    d.style.color = isError ? '#ffb3b3' : '#bfffe8';
    el.appendChild(d);
  }
  if (isError) console.error(msg); else console.log(msg);
}

let subtitleTimeout = null;
let subtitleWords = [];
let subtitleIndex = 0;

function showResponse(message, heard, useSubtitle = true){
  const heardPart = heard ? `Heard "${heard}". ` : '';
  console.log(`[Response] ${heardPart}${message}`);
}

function speakResponse(message){
  if (!('speechSynthesis' in window)) return;
  resetIdleTimer(); // Reset idle timer when Avril speaks
  const utterance = new SpeechSynthesisUtterance(message);
  utterance.lang = 'en-GB';
  // Adjust pacing based on response length:
  // - short confirmations a bit faster
  // - long informational replies a bit slower
  const len = message ? message.length : 0;
  if (len <= 40){
    utterance.rate = 1.1;
  } else if (len >= 160){
    utterance.rate = 0.9;
  } else {
    utterance.rate = 1;
  }
  utterance.pitch = 0.9;
  utterance.volume = 1;
  if (selectedVoice) utterance.voice = selectedVoice;
  // ensure any previous speech is cancelled, then speak and mark busy
  window.speechSynthesis.cancel();

  // While Avril is speaking, pause recognition so we don't hear our own TTS
  if (speechRecognition && recognitionActive){
    stopSpeechRecognition();
    recognitionPausedForSpeech = true;
  } else {
    recognitionPausedForSpeech = false;
  }

  isSpeaking = true;
  utterance.onend = () => {
    isSpeaking = false;
    if (micMode === 'stream' && (micMutedForCommand || recognitionPausedForSpeech)){
      startSpeechRecognition();
    }
    micMutedForCommand = false;
    recognitionPausedForSpeech = false;
  };
  utterance.onerror = () => {
    isSpeaking = false;
    if (micMode === 'stream' && (micMutedForCommand || recognitionPausedForSpeech)){
      startSpeechRecognition();
    }
    micMutedForCommand = false;
    recognitionPausedForSpeech = false;
  };
  window.speechSynthesis.speak(utterance);
}

function setWakeState(active){
  wakeActive = active;
  clearTimeout(wakeResetTimer);
  if (active){
    // continuous session until explicitly closed
    wakeResetTimer = null;
  } else {
    wakeResetTimer = null;
  }
}

async function acknowledgeWake(heard){
  hideSleepScreen(); // Hide sleep screen when wake-up command is issued
  resetIdleTimer(); // Reset idle timer
  setWakeState(true);
  sessionActive = true;
  expectImmediateCommand = true;
  setListening(true);

   // Chime to confirm wake phrase was recognised
  playStartChime();

  const msg = 'What is your command?';
  speakResponse(msg);
}

function resetWakeState(){
  setWakeState(false);
  sessionActive = false;
  expectImmediateCommand = false;
  // Chime softly when session ends
  playStopChime();
}

// Mic button state helper
function setMicState(state){
  const btn = document.getElementById('startBtn');
  if (btn){
    btn.classList.remove('idle','requesting','on','fallback','muted');
  btn.classList.add(state);
  if (state === 'requesting'){
    btn.setAttribute('aria-label','Requesting microphone access');
    btn.title = 'Requesting microphone access';
  } else if (state === 'on'){
    btn.setAttribute('aria-label','Microphone on');
    btn.title = 'Microphone on';
  } else if (state === 'fallback'){
    btn.setAttribute('aria-label','Audio fallback active');
    btn.title = 'Audio fallback active';
    } else if (state === 'muted'){
      btn.setAttribute('aria-label','Microphone muted');
      btn.title = 'Microphone muted';
  } else {
    btn.setAttribute('aria-label','Start microphone');
    btn.title = 'Start microphone';
  }
  }

  let statusText = 'Idle';
  if (state === 'requesting') statusText = 'Requesting access';
  else if (state === 'on') statusText = 'Live listening';
  else if (state === 'fallback') statusText = 'Fallback tone';
  else if (state === 'muted') statusText = 'Muted';
  updateStatusText(statusText);
}

function updateStatusText(text){
  if (micStatusEl) micStatusEl.textContent = text;
  if (brandStatusEl) brandStatusEl.textContent = text;
}

function getAudioAmplitude(){
  if (!analyser) return 0;
  analyser.getByteFrequencyData(dataArray);
  let sum = 0;
  for (let i = 0; i < dataArray.length; i++) sum += dataArray[i];
  const avg = sum / dataArray.length; // 0..255
  return avg / 255; // normalized 0..1
}

// Orb vertex shader using simplex noise (GLSL)
function vertexShader(){
  return `
    uniform float uTime;
    uniform float uAmp;
    varying vec3 vNormal;
    varying vec3 vPos;

    // Simplex noise (Ashima 3D - compact version)
    vec3 mod289(vec3 x){return x - floor(x * (1.0 / 289.0)) * 289.0;}
    vec4 mod289(vec4 x){return x - floor(x * (1.0 / 289.0)) * 289.0;}
    vec4 permute(vec4 x){return mod289(((x*34.0)+1.0)*x);} 
    float snoise(vec3 v){
      const vec2  C = vec2(1.0/6.0, 1.0/3.0);
      const vec4  D = vec4(0.0, 0.5, 1.0, 2.0);
      vec3 i  = floor(v + dot(v, C.yyy) );
      vec3 x0 = v - i + dot(i, C.xxx);
      vec3 g = step(x0.yzx, x0.xyz);
      vec3 l = 1.0 - g;
      vec3 i1 = min( g.xyz, l.zxy );
      vec3 i2 = max( g.xyz, l.zxy );
      vec3 x1 = x0 - i1 + C.xxx;
      vec3 x2 = x0 - i2 + C.yyy;
      vec3 x3 = x0 - D.yyy;
      i = mod289(i);
      vec4 p = permute( permute( permute(
                 i.z + vec4(0.0, i1.z, i2.z, 1.0 ))
               + i.y + vec4(0.0, i1.y, i2.y, 1.0 ))
               + i.x + vec4(0.0, i1.x, i2.x, 1.0 ));
      float n_ = 1.0/7.0;
      vec3 ns = n_ * D.wyz - D.xzx;
      vec4 j = p - 49.0 * floor(p * ns.z * ns.z);
      vec4 x_ = floor(j * ns.z);
      vec4 y_ = floor(j - 7.0 * x_ );
      vec4 x = x_ *ns.x + ns.yyyy;
      vec4 y = y_ *ns.x + ns.yyyy;
      vec4 h = 1.0 - abs(x) - abs(y);
      vec4 b0 = vec4( x.xy, y.xy );
      vec4 b1 = vec4( x.zw, y.zw );
      vec4 s0 = floor(b0)*2.0 + 1.0;
      vec4 s1 = floor(b1)*2.0 + 1.0;
      vec4 sh = -step(h, vec4(0.0));
      vec4 a0 = b0.xzyw + s0.xzyw*sh.xxyy;
      vec4 a1 = b1.xzyw + s1.xzyw*sh.zzww;
      vec3 p0 = vec3(a0.xy,h.x);
      vec3 p1 = vec3(a0.zw,h.y);
      vec3 p2 = vec3(a1.xy,h.z);
      vec3 p3 = vec3(a1.zw,h.w);
      vec4 norm = 1.79284291400159 - 0.85373472095314 *
        vec4(dot(p0,p0), dot(p1,p1), dot(p2,p2), dot(p3,p3));
      p0 *= norm.x;
      p1 *= norm.y;
      p2 *= norm.z;
      p3 *= norm.w;
      vec4 m = max(0.6 - vec4(dot(x0,x0), dot(x1,x1), dot(x2,x2), dot(x3,x3)), 0.0);
      m = m * m;
      return 42.0 * dot( m*m, vec4( dot(p0,x0), dot(p1,x1), dot(p2,x2), dot(p3,x3) ) );
    }

    void main(){
      vNormal = normal;
      vPos = position;
      float a = uAmp;
      float noiseScale = 1.6;
      float n = snoise(position * noiseScale + vec3(0.0, uTime*0.6, uTime*0.3));
      float displacement = n * (0.9 + a * 1.8);
      vec3 newPos = position + normal * displacement;
      gl_Position = projectionMatrix * modelViewMatrix * vec4(newPos, 1.0);
    }
  `;
}

function fragmentShader(){
  return `
    uniform float uTime;
    uniform float uAmp;
    varying vec3 vNormal;
    varying vec3 vPos;

    vec3 hsv2rgb(vec3 c){
      vec3 rgb = clamp( abs(mod(c.x*6.0 + vec3(0.0,4.0,2.0), 6.0)-3.0)-1.0, 0.0, 1.0 );
      rgb = rgb*rgb*(3.0-2.0*rgb);
      return c.z * mix(vec3(1.0), rgb, c.y);
    }

    void main(){
      vec3 n = normalize(vNormal);
      float ndotl = dot(n, vec3(0.0, 0.0, 1.0));
      float intensity = pow(abs(ndotl), 1.4);

      float radius = length(vPos);
      float audioGlow = smoothstep(0.0, 1.0, uAmp * 2.8 + radius * 0.06);

      // Shift hue subtly with audio and position to get a cohesive cyan/teal tone
      float baseHue = 0.47;                 // cyan/teal
      float hueShift = -0.15 * uAmp + 0.03 * sin(uTime*1.4 + radius*3.5);
      float innerHue = baseHue + hueShift;
      float outerHue = innerHue;            // keep same hue at edge (no blue gradient)

      float sat = mix(0.7, 1.0, audioGlow);
      float valInner = 0.95;
      float valOuter = 0.7;

      vec3 innerColor = hsv2rgb(vec3(innerHue, sat, valInner));
      vec3 outerColor = hsv2rgb(vec3(outerHue, sat, valOuter)); // same hue, just a bit darker

      // Blend from center to edge and add a soft rim light
      float edge = smoothstep(0.6, 1.2, radius);
      vec3 base = mix(innerColor, outerColor, edge);

      float rim = pow(1.0 - abs(ndotl), 3.0);
      base += innerColor * rim * 0.25;

      // Slight pulse on audio peaks
      float pulse = 0.12 * smoothstep(0.25, 0.9, uAmp);
      base *= (1.0 + pulse);

      gl_FragColor = vec4(base * intensity, 1.0);
    }
  `;
}

// Points shaders
function pointsVertexShader(){
  return `
    uniform float uTime;
    uniform float uAmp;
    varying vec3 vColor;

    float pnoise(vec3 p){
      return sin(p.x*3.0 + uTime*1.8) * 0.5 + sin(p.y*4.5 + uTime*1.2)*0.25 + sin(p.z*2.3 + uTime*2.2)*0.25;
    }

    void main(){
      vColor = color;
      vec3 pos = position;
      float n = pnoise(pos + vec3(uTime*0.05));
      float amp = uAmp * 0.9;
      vec3 p = pos + normalize(pos) * n * (0.3 + amp*0.9);
      vec4 mvPosition = modelViewMatrix * vec4(p, 1.0);
      gl_PointSize = (2.0 + 8.0 * (0.2 + amp)) * (300.0 / -mvPosition.z);
      gl_Position = projectionMatrix * mvPosition;
    }
  `;
}

function pointsFragmentShader(){
  return `
    varying vec3 vColor;
    void main(){
      float r = length(gl_PointCoord - vec2(0.5));
      float alpha = smoothstep(0.5, 0.1, r);
      vec3 col = vColor;
      gl_FragColor = vec4(col, alpha*0.9);
    }
  `;
}
