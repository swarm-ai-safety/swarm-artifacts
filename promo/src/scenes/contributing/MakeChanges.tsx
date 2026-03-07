import React from "react";
import { AbsoluteFill, useCurrentFrame, spring, interpolate } from "remotion";
import { colors, fonts } from "../../theme";

const workflow = [
  { step: "Create a branch", cmd: "git checkout -b feature/your-feature" },
  { step: "Write your code", cmd: "swarm/agents/your_agent.py" },
  { step: "Add tests", cmd: "tests/test_your_agent.py" },
  { step: "Run the test suite", cmd: "pytest tests/ -v" },
  { step: "Check linting", cmd: "ruff check swarm/ tests/" },
  { step: "Check types", cmd: "mypy swarm/" },
];

export const MakeChanges: React.FC = () => {
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
        Step 4
      </div>

      <div
        style={{
          fontSize: 64,
          fontWeight: 800,
          color: colors.text,
          opacity: headerProgress,
          marginBottom: 50,
        }}
      >
        Make Your Changes
      </div>

      <div style={{ maxWidth: 900, width: "100%" }}>
        {workflow.map((item, i) => {
          const delay = 15 + i * 20;
          const progress = spring({
            frame: frame - delay,
            fps: 30,
            config: { damping: 200 },
          });
          const p = Math.max(0, progress);

          // Highlight current step
          const isActive =
            frame >= delay + 10 && (i === workflow.length - 1 || frame < 15 + (i + 1) * 20 + 10);

          return (
            <div
              key={i}
              style={{
                display: "flex",
                alignItems: "center",
                gap: 20,
                marginBottom: 20,
                opacity: p,
                transform: `translateX(${interpolate(p, [0, 1], [-30, 0])}px)`,
              }}
            >
              <div
                style={{
                  width: 40,
                  height: 40,
                  borderRadius: "50%",
                  background: isActive ? colors.accent : `${colors.accent}30`,
                  display: "flex",
                  alignItems: "center",
                  justifyContent: "center",
                  fontSize: 20,
                  fontWeight: 700,
                  color: isActive ? colors.bg : colors.accent,
                  transition: "all 0.3s",
                  flexShrink: 0,
                }}
              >
                {i + 1}
              </div>

              <div style={{ flex: 1 }}>
                <div
                  style={{
                    fontSize: 24,
                    fontWeight: 600,
                    color: isActive ? colors.text : colors.textDim,
                    marginBottom: 4,
                  }}
                >
                  {item.step}
                </div>
                <div
                  style={{
                    fontSize: 18,
                    fontFamily: fonts.mono,
                    color: isActive ? colors.accent : colors.textMuted,
                  }}
                >
                  {item.cmd}
                </div>
              </div>

              {i < workflow.length - 1 && (
                <div
                  style={{
                    position: "absolute",
                    left: 99,
                    top: 0,
                    width: 2,
                    height: 20,
                    background: `${colors.accent}20`,
                  }}
                />
              )}
            </div>
          );
        })}
      </div>
    </AbsoluteFill>
  );
};
