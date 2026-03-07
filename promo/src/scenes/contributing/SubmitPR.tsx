import React from "react";
import { AbsoluteFill, useCurrentFrame, spring, interpolate } from "remotion";
import { colors, fonts } from "../../theme";

const checklist = [
  { text: "All tests pass", cmd: "pytest tests/ -v" },
  { text: "Linting passes", cmd: "ruff check swarm/ tests/" },
  { text: "Type checking passes", cmd: "mypy swarm/" },
  { text: "New code has tests", cmd: "" },
];

const prSteps = [
  "git add your-changed-files",
  "git commit -m \"feat: add your feature\"",
  "git push origin feature/your-feature",
  "Open a Pull Request on GitHub",
];

export const SubmitPR: React.FC = () => {
  const frame = useCurrentFrame();

  const headerProgress = spring({ frame, fps: 30, config: { damping: 200 } });

  return (
    <AbsoluteFill
      style={{
        background: colors.bg,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        justifyContent: "center",
        fontFamily: fonts.heading,
        padding: 80,
      }}
    >
      <div
        style={{
          position: "absolute",
          inset: 0,
          backgroundImage: `
            linear-gradient(${colors.gridLine} 1px, transparent 1px),
            linear-gradient(90deg, ${colors.gridLine} 1px, transparent 1px)
          `,
          backgroundSize: "80px 80px",
          opacity: 0.2,
        }}
      />

      <div
        style={{
          fontSize: 28,
          fontWeight: 600,
          color: colors.accent,
          letterSpacing: "0.15em",
          textTransform: "uppercase",
          opacity: headerProgress,
          marginBottom: 8,
        }}
      >
        Step 5
      </div>

      <div
        style={{
          fontSize: 64,
          fontWeight: 800,
          color: colors.text,
          opacity: headerProgress,
          marginBottom: 40,
        }}
      >
        Submit Your PR
      </div>

      <div
        style={{
          display: "flex",
          gap: 40,
          maxWidth: 1100,
          width: "100%",
        }}
      >
        {/* Checklist */}
        <div style={{ flex: 1 }}>
          <div
            style={{
              fontSize: 26,
              fontWeight: 700,
              color: colors.warning,
              marginBottom: 20,
              opacity: Math.max(
                0,
                spring({ frame: frame - 10, fps: 30, config: { damping: 200 } }),
              ),
            }}
          >
            Pre-flight Checklist
          </div>

          {checklist.map((item, i) => {
            const delay = 20 + i * 18;
            const progress = spring({
              frame: frame - delay,
              fps: 30,
              config: { damping: 200 },
            });
            const p = Math.max(0, progress);

            const checked = frame > delay + 20;

            return (
              <div
                key={i}
                style={{
                  display: "flex",
                  alignItems: "center",
                  gap: 14,
                  marginBottom: 16,
                  opacity: p,
                }}
              >
                <div
                  style={{
                    width: 28,
                    height: 28,
                    borderRadius: 6,
                    border: `2px solid ${checked ? colors.success : colors.textMuted}`,
                    background: checked ? `${colors.success}20` : "transparent",
                    display: "flex",
                    alignItems: "center",
                    justifyContent: "center",
                    fontSize: 16,
                    color: colors.success,
                    flexShrink: 0,
                  }}
                >
                  {checked ? "\u2713" : ""}
                </div>
                <div>
                  <div style={{ fontSize: 20, color: colors.text }}>{item.text}</div>
                  {item.cmd && (
                    <div
                      style={{
                        fontSize: 14,
                        fontFamily: fonts.mono,
                        color: colors.textMuted,
                      }}
                    >
                      {item.cmd}
                    </div>
                  )}
                </div>
              </div>
            );
          })}
        </div>

        {/* Push & PR */}
        <div style={{ flex: 1 }}>
          <div
            style={{
              fontSize: 26,
              fontWeight: 700,
              color: colors.success,
              marginBottom: 20,
              opacity: Math.max(
                0,
                spring({ frame: frame - 10, fps: 30, config: { damping: 200 } }),
              ),
            }}
          >
            Push & Open PR
          </div>

          {prSteps.map((step, i) => {
            const delay = 80 + i * 18;
            const progress = spring({
              frame: frame - delay,
              fps: 30,
              config: { damping: 200 },
            });
            const p = Math.max(0, progress);

            return (
              <div
                key={i}
                style={{
                  display: "flex",
                  alignItems: "center",
                  gap: 14,
                  marginBottom: 18,
                  opacity: p,
                  transform: `translateX(${interpolate(p, [0, 1], [20, 0])}px)`,
                }}
              >
                <div
                  style={{
                    width: 30,
                    height: 30,
                    borderRadius: "50%",
                    background: `${colors.success}20`,
                    border: `2px solid ${colors.success}40`,
                    display: "flex",
                    alignItems: "center",
                    justifyContent: "center",
                    fontSize: 16,
                    fontWeight: 700,
                    color: colors.success,
                    flexShrink: 0,
                  }}
                >
                  {i + 1}
                </div>
                <div
                  style={{
                    fontSize: 19,
                    fontFamily: i < 3 ? fonts.mono : fonts.heading,
                    color: i < 3 ? colors.accent : colors.text,
                    fontWeight: i === 3 ? 600 : 400,
                  }}
                >
                  {step}
                </div>
              </div>
            );
          })}
        </div>
      </div>
    </AbsoluteFill>
  );
};
