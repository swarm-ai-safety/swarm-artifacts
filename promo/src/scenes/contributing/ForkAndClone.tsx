import React from "react";
import { AbsoluteFill, useCurrentFrame, spring, interpolate } from "remotion";
import { colors, fonts } from "../../theme";

const steps = [
  {
    label: "1. Fork the repo",
    code: "Click 'Fork' on github.com/swarm-ai-safety/swarm",
    icon: "\u{1F374}",
  },
  {
    label: "2. Clone your fork",
    code: "git clone https://github.com/YOUR-USERNAME/swarm.git",
    icon: "\u{1F4E5}",
  },
  {
    label: "3. Enter the directory",
    code: "cd swarm",
    icon: "\u{1F4C2}",
  },
  {
    label: "4. Add upstream remote",
    code: "git remote add upstream https://github.com/swarm-ai-safety/swarm.git",
    icon: "\u{1F517}",
  },
];

export const ForkAndClone: React.FC = () => {
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
        Step 1
      </div>

      <div
        style={{
          fontSize: 64,
          fontWeight: 800,
          color: colors.text,
          opacity: headerProgress,
          marginBottom: 60,
        }}
      >
        Fork & Clone
      </div>

      {steps.map((step, i) => {
        const delay = 20 + i * 25;
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
              gap: 24,
              marginBottom: 28,
              opacity: p,
              transform: `translateX(${interpolate(p, [0, 1], [-40, 0])}px)`,
              width: "100%",
              maxWidth: 1000,
            }}
          >
            <div style={{ fontSize: 36 }}>{step.icon}</div>
            <div>
              <div
                style={{
                  fontSize: 26,
                  fontWeight: 600,
                  color: colors.text,
                  marginBottom: 6,
                }}
              >
                {step.label}
              </div>
              <div
                style={{
                  fontSize: 22,
                  fontFamily: fonts.mono,
                  color: colors.accent,
                  background: `${colors.accent}10`,
                  padding: "8px 16px",
                  borderRadius: 8,
                  borderLeft: `3px solid ${colors.accent}`,
                }}
              >
                {step.code}
              </div>
            </div>
          </div>
        );
      })}
    </AbsoluteFill>
  );
};
