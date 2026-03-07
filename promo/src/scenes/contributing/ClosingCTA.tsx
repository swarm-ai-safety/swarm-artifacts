import React from "react";
import { AbsoluteFill, useCurrentFrame, spring, interpolate } from "remotion";
import { colors, fonts } from "../../theme";

export const ClosingCTA: React.FC = () => {
  const frame = useCurrentFrame();

  const gradientX = interpolate(frame, [0, 180], [40, 60]);

  const titleProgress = spring({ frame, fps: 30, config: { damping: 200 } });

  const urlProgress = spring({
    frame: frame - 30,
    fps: 30,
    config: { damping: 200 },
  });
  const url = Math.max(0, urlProgress);

  const items = [
    "Star the repo",
    "Pick a good first issue",
    "Submit your first PR",
    "Join the community",
  ];

  // Pulsing glow on the URL
  const glowOpacity = interpolate(
    Math.sin(frame * 0.08),
    [-1, 1],
    [0.3, 0.8],
  );

  return (
    <AbsoluteFill
      style={{
        background: `radial-gradient(ellipse at ${gradientX}% 50%, ${colors.accentDim}20, ${colors.bg} 70%)`,
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
          opacity: 0.3,
        }}
      />

      <div
        style={{
          fontSize: 64,
          fontWeight: 800,
          color: colors.text,
          opacity: titleProgress,
          marginBottom: 16,
          textAlign: "center",
        }}
      >
        Start Contributing Today
      </div>

      <div
        style={{
          width: interpolate(
            spring({ frame: frame - 10, fps: 30, config: { damping: 100 } }),
            [0, 1],
            [0, 400],
          ),
          height: 2,
          background: `linear-gradient(90deg, transparent, ${colors.accent}, transparent)`,
          marginBottom: 50,
        }}
      />

      <div
        style={{
          display: "flex",
          gap: 30,
          marginBottom: 60,
        }}
      >
        {items.map((item, i) => {
          const delay = 25 + i * 15;
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
                background: `${colors.accent}10`,
                border: `1px solid ${colors.accent}30`,
                borderRadius: 12,
                padding: "16px 24px",
                fontSize: 22,
                color: colors.text,
                fontWeight: 600,
                opacity: p,
                transform: `translateY(${interpolate(p, [0, 1], [20, 0])}px)`,
              }}
            >
              {item}
            </div>
          );
        })}
      </div>

      <div
        style={{
          fontSize: 36,
          fontFamily: fonts.mono,
          fontWeight: 700,
          color: colors.accent,
          opacity: url,
          transform: `scale(${interpolate(url, [0, 1], [0.9, 1])})`,
          textShadow: `0 0 40px ${colors.accent}${Math.round(glowOpacity * 255)
            .toString(16)
            .padStart(2, "0")}`,
        }}
      >
        github.com/swarm-ai-safety/swarm
      </div>

      <div
        style={{
          fontSize: 22,
          color: colors.textDim,
          marginTop: 30,
          opacity: Math.max(
            0,
            spring({
              frame: frame - 70,
              fps: 30,
              config: { damping: 200 },
            }),
          ),
          fontStyle: "italic",
        }}
      >
        Help build safer multi-agent AI systems
      </div>
    </AbsoluteFill>
  );
};
