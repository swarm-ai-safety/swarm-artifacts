import React from "react";
import { AbsoluteFill, useCurrentFrame, spring, interpolate } from "remotion";
import { colors, fonts } from "../../theme";

const labels = [
  {
    name: "good first issue",
    color: colors.success,
    description: "Perfect for newcomers",
  },
  {
    name: "help wanted",
    color: colors.warning,
    description: "Maintainers need assistance",
  },
  {
    name: "agent-bounty",
    color: colors.accent,
    description: "Designed for AI coding agents",
  },
  {
    name: "bug",
    color: colors.danger,
    description: "Something isn't working right",
  },
];

export const FindIssue: React.FC = () => {
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
        Step 3
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
        Find an Issue
      </div>

      <div
        style={{
          fontSize: 24,
          color: colors.textDim,
          opacity: headerProgress,
          marginBottom: 50,
          textAlign: "center",
          maxWidth: 700,
        }}
      >
        Browse GitHub Issues and look for these labels:
      </div>

      <div
        style={{
          display: "flex",
          flexDirection: "column",
          gap: 24,
          maxWidth: 800,
          width: "100%",
        }}
      >
        {labels.map((label, i) => {
          const delay = 25 + i * 20;
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
                opacity: p,
                transform: `translateY(${interpolate(p, [0, 1], [30, 0])}px)`,
              }}
            >
              <div
                style={{
                  background: `${label.color}20`,
                  border: `2px solid ${label.color}`,
                  borderRadius: 20,
                  padding: "8px 20px",
                  fontSize: 20,
                  fontWeight: 700,
                  color: label.color,
                  fontFamily: fonts.mono,
                  minWidth: 220,
                  textAlign: "center",
                }}
              >
                {label.name}
              </div>
              <div
                style={{
                  fontSize: 24,
                  color: colors.textDim,
                }}
              >
                {label.description}
              </div>
            </div>
          );
        })}
      </div>

      <div
        style={{
          fontSize: 20,
          color: colors.textMuted,
          marginTop: 50,
          opacity: Math.max(
            0,
            spring({
              frame: frame - 110,
              fps: 30,
              config: { damping: 200 },
            }),
          ),
          fontFamily: fonts.mono,
        }}
      >
        github.com/swarm-ai-safety/swarm/issues
      </div>
    </AbsoluteFill>
  );
};
