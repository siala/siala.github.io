document.addEventListener("DOMContentLoaded", () => {
  const themes = new Set(["academic", "oxford", "forest", "graphite", "aubergine", "terracotta", "nordic", "teal", "burgundy", "sepia"]);
  const textStyles = new Set(["balanced", "classic", "modern", "scholarly", "compact", "spacious"]);
  const backgrounds = new Set(["paper", "ivory", "gray", "mist", "sage", "sand", "rose", "lavender"]);
  const themeSelect = document.querySelector("#theme-select");
  const textStyleSelect = document.querySelector("#text-style-select");
  const backgroundSelect = document.querySelector("#background-select");

  let theme = "academic";
  let textStyle = "balanced";
  let background = "paper";
  try {
    const savedTheme = localStorage.getItem("ms-theme");
    const savedTextStyle = localStorage.getItem("ms-text-style");
    const savedBackground = localStorage.getItem("ms-background");
    if (themes.has(savedTheme)) theme = savedTheme;
    if (textStyles.has(savedTextStyle)) textStyle = savedTextStyle;
    if (backgrounds.has(savedBackground)) background = savedBackground;
  } catch {}

  document.documentElement.dataset.theme = theme;
  document.documentElement.dataset.textStyle = textStyle;
  document.documentElement.dataset.background = background;
  if (themeSelect) themeSelect.value = theme;
  if (textStyleSelect) textStyleSelect.value = textStyle;
  if (backgroundSelect) backgroundSelect.value = background;

  themeSelect?.addEventListener("change", () => {
    document.documentElement.dataset.theme = themeSelect.value;
    try { localStorage.setItem("ms-theme", themeSelect.value); } catch {}
  });

  textStyleSelect?.addEventListener("change", () => {
    document.documentElement.dataset.textStyle = textStyleSelect.value;
    try { localStorage.setItem("ms-text-style", textStyleSelect.value); } catch {}
  });

  backgroundSelect?.addEventListener("change", () => {
    document.documentElement.dataset.background = backgroundSelect.value;
    try { localStorage.setItem("ms-background", backgroundSelect.value); } catch {}
  });

  // Header "Theme" menu. A preset is a whole look and overrides the palette,
  // background and text-style chosen in the footer panel; "classic" removes the
  // attribute entirely so those controls take over again.
  const presets = new Set(["classic", "dark", "cheerful", "bright", "newsprint"]);
  const presetSelect = document.querySelector("#preset-select");
  let preset = "newsprint";
  try {
    const saved = localStorage.getItem("ms-preset");
    if (presets.has(saved)) preset = saved;
  } catch {}

  const applyPreset = (value) => {
    if (value === "classic") delete document.documentElement.dataset.preset;
    else document.documentElement.dataset.preset = value;
  };

  applyPreset(preset);
  if (presetSelect) presetSelect.value = preset;

  presetSelect?.addEventListener("change", () => {
    applyPreset(presetSelect.value);
    try { localStorage.setItem("ms-preset", presetSelect.value); } catch {}
  });

  // The news list scrolls inside a fixed height. Overlay scrollbars hide themselves
  // when idle, so the panel is faded at the bottom to show the list continues; the
  // fade lifts once the reader reaches the end.
  const newsList = document.querySelector(".legacy-home .panel-phd > .panel-body > ul");
  if (newsList) {
    const newsPanel = newsList.parentElement;
    const syncNewsFade = () => {
      const remaining = newsList.scrollHeight - newsList.scrollTop - newsList.clientHeight;
      newsPanel.dataset.scrollEnd = String(remaining <= 2);
    };
    newsList.addEventListener("scroll", syncNewsFade, { passive: true });
    window.addEventListener("resize", syncNewsFade);
    syncNewsFade();
  }

  const root = document.querySelector(".publications-content");
  if (!root) return;

  const checkboxes = Array.from(root.querySelectorAll("#tag-filters input[type='checkbox']"));
  const publications = Array.from(root.querySelectorAll(".pub"));

  const update = () => {
    const selected = checkboxes.filter((input) => input.checked).map((input) => input.value);

    checkboxes.forEach((input) => {
      input.closest("label")?.classList.toggle("active", input.checked);
    });

    publications.forEach((publication) => {
      const tags = new Set(
        (publication.dataset.tags || "").split(",").map((tag) => tag.trim()).filter(Boolean),
      );
      publication.hidden = selected.length > 0 && !selected.some((tag) => tags.has(tag));
    });

    root.querySelectorAll(".well").forEach((group) => {
      if (group.id === "filter-section") return;
      const items = Array.from(group.querySelectorAll(".pub"));
      if (items.length) group.hidden = items.every((item) => item.hidden);
    });
  };

  checkboxes.forEach((input) => input.addEventListener("change", update));
  update();
});
