import React from "react";
import { AbsoluteFill, useCurrentFrame, spring, interpolate } from "remotion";
import { colors, fonts } from "../../theme";

export const GameHook: React.FC = () => {
  const frame = useCurrentFrame();

  const gradientY = interpolate(frame, [0, 150], [40, 60]);

  // Title springs in
  const titleP = spring({ frame, fps: 30, config: { damping: 200 } });
  const titleScale = interpolate(titleP, [0, 1], [0.6, 1]);

  // Subtitle fades up
  const subP = Math.max(
    0,
    spring({ frame: frame - 25, fps: 30, config: { damping: 200 } }),
  );

  // Grid lines animate in
  const gridP = Math.max(
    0,
    spring({ frame: frame - 10, fps: 30, config: { damping: 100 } }),
  );

  // Pulsing accent glow
  const pulse = Math.sin(frame * 0.08) * 0.3 + 0.7;

  // Isometric grid lines
  const isoLines = Array.from({ length: 12 }, (_, i) => i);

  return (
    <AbsoluteFill
      style={{
        background: `radial-gradient(ellipse at 50% ${gradientY}%, ${colors.accentDim}20, ${colors.bg} 70%)`,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        justifyContent: "center",
        fontFamily: fonts.heading,
      }}
    >
      {/* Standard grid overlay */}
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

      {/* Isometric grid lines in background */}
      <svg
        style={{ position: "absolute", inset: 0, opacity: gridP * 0.15 }}
        viewBox="0 0 1080 1920"
      >
        {isoLines.map((i) => {
          const y = 1200 + i * 60;
          const spread = interpolate(gridP, [0, 1], [0, 540]);
          return (
            <React.Fragment key={i}>
              <line
                x1={540 - spread}
                y1={y - spread * 0.5}
                x2={540 + spread}
                y2={y - spread * 0.5}
                stroke={colors.accent}
                strokeWidth={1}
                opacity={interpolate(i, [0, 11], [0.6, 0.1])}
              />
              <line
                x1={540 - spread}
                y1={y + spread * 0.3}
                x2={540 + spread}
                y2={y + spread * 0.3}
                stroke={colors.accent}
                strokeWidth={1}
                opacity={interpolate(i, [0, 11], [0.4, 0.05])}
              />
            </React.Fragment>
          );
        })}
      </svg>

      {/* Pulsing glow behind title */}
      <div
        style={{
          position: "absolute",
          width: 500,
          height: 500,
          borderRadius: "50%",
          background: `radial-gradient(circle, ${colors.accent}${Math.round(pulse * 12).toString(16).padStart(2, "0")}, transparent 70%)`,
          top: "35%",
          left: "50%",
          transform: "translate(-50%, -50%)",
        }}
      />

      {/* SWARM title */}
      <div
        style={{
          fontSize: 160,
          fontWeight: 800,
          color: colors.text,
          letterSpacing: "0.2em",
          opacity: titleP,
          transform: `scale(${titleScale})`,
          textShadow: `0 0 60px ${colors.accent}40`,
          zIndex: 1,
        }}
      >
        SWARM
      </div>

      {/* Accent line */}
      <div
        style={{
          width: interpolate(
            Math.max(0, spring({ frame: frame - 15, fps: 30, config: { damping: 100 } })),
            [0, 1],
            [0, 300],
          ),
          height: 3,
          background: `linear-gradient(90deg, transparent, ${colors.accent}, transparent)`,
          marginTop: 20,
          marginBottom: 30,
          zIndex: 1,
        }}
      />

      {/* Subtitle */}
      <div
        style={{
          fontSize: 52,
          fontWeight: 600,
          color: colors.accent,
          opacity: subP,
          transform: `translateY(${interpolate(subP, [0, 1], [30, 0])}px)`,
          textAlign: "center",
          zIndex: 1,
          lineHeight: 1.4,
        }}
      >
        Can you govern
        <br />
        AI agents?
      </div>
    </AbsoluteFill>
  );
};
