import React from "react";
import { AbsoluteFill, useCurrentFrame, spring, interpolate } from "remotion";
import { colors, fonts } from "../../theme";

export const PlayNow: React.FC = () => {
  const frame = useCurrentFrame();

  const gradientX = interpolate(frame, [0, 240], [30, 70]);

  // Logo
  const logoP = spring({ frame, fps: 30, config: { damping: 200 } });
  const logoScale = interpolate(logoP, [0, 1], [0.7, 1]);

  // "Play Now" text
  const playP = Math.max(
    0,
    spring({ frame: frame - 20, fps: 30, config: { damping: 200 } }),
  );

  // URL
  const urlP = Math.max(
    0,
    spring({ frame: frame - 40, fps: 30, config: { damping: 200 } }),
  );

  // QR placeholder
  const qrP = Math.max(
    0,
    spring({ frame: frame - 55, fps: 30, config: { damping: 200 } }),
  );

  // Bottom tagline
  const tagP = Math.max(
    0,
    spring({ frame: frame - 70, fps: 30, config: { damping: 200 } }),
  );

  // Pulsing CTA glow
  const pulse = Math.sin(frame * 0.1) * 0.4 + 0.6;

  return (
    <AbsoluteFill
      style={{
        background: `radial-gradient(ellipse at ${gradientX}% 45%, ${colors.accentDim}18, ${colors.bg} 70%)`,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        justifyContent: "center",
        fontFamily: fonts.heading,
      }}
    >
      {/* Grid overlay */}
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

      {/* SWARM logo */}
      <div
        style={{
          fontSize: 120,
          fontWeight: 800,
          color: colors.text,
          letterSpacing: "0.18em",
          opacity: logoP,
          transform: `scale(${logoScale})`,
          textShadow: `0 0 40px ${colors.accent}30`,
          marginBottom: 50,
          zIndex: 1,
        }}
      >
        SWARM
      </div>

      {/* Play Now text */}
      <div
        style={{
          fontSize: 48,
          fontWeight: 600,
          color: colors.text,
          opacity: playP,
          transform: `translateY(${interpolate(playP, [0, 1], [20, 0])}px)`,
          marginBottom: 12,
          zIndex: 1,
        }}
      >
        Play Now
      </div>

      <div
        style={{
          fontSize: 30,
          color: colors.textDim,
          opacity: playP,
          marginBottom: 40,
          zIndex: 1,
        }}
      >
        Free in your browser
      </div>

      {/* URL */}
      <div
        style={{
          opacity: urlP,
          background: `${colors.textMuted}20`,
          border: `2px solid ${colors.accent}${Math.round(pulse * 80).toString(16).padStart(2, "0")}`,
          borderRadius: 16,
          padding: "20px 48px",
          marginBottom: 50,
          boxShadow: `0 0 30px ${colors.accent}${Math.round(pulse * 20).toString(16).padStart(2, "0")}`,
          zIndex: 1,
        }}
      >
        <span
          style={{
            fontSize: 40,
            fontFamily: fonts.mono,
            color: colors.accent,
            fontWeight: 600,
          }}
        >
          swarm-ai.org/game/
        </span>
      </div>

      {/* QR code placeholder */}
      <div
        style={{
          width: 200,
          height: 200,
          border: `2px solid ${colors.accent}40`,
          borderRadius: 12,
          opacity: qrP * 0.8,
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
          marginBottom: 50,
          zIndex: 1,
          background: `${colors.bg}80`,
        }}
      >
        {/* Simple QR-like pattern */}
        <svg width={160} height={160} viewBox="0 0 160 160">
          {/* Corner squares */}
          {[
            [10, 10],
            [110, 10],
            [10, 110],
          ].map(([x, y], i) => (
            <React.Fragment key={i}>
              <rect
                x={x}
                y={y}
                width={40}
                height={40}
                fill="none"
                stroke={colors.accent}
                strokeWidth={3}
                rx={4}
              />
              <rect
                x={x + 10}
                y={y + 10}
                width={20}
                height={20}
                fill={colors.accent}
                rx={2}
              />
            </React.Fragment>
          ))}
          {/* Center dots */}
          {Array.from({ length: 5 }, (_, row) =>
            Array.from({ length: 5 }, (_, col) => {
              const on = (row + col) % 2 === 0;
              if (!on) return null;
              return (
                <rect
                  key={`${row}-${col}`}
                  x={60 + col * 10}
                  y={60 + row * 10}
                  width={8}
                  height={8}
                  fill={colors.accent}
                  opacity={0.6}
                  rx={1}
                />
              );
            }),
          )}
        </svg>
      </div>

      {/* Bottom tagline */}
      <div
        style={{
          fontSize: 26,
          color: colors.textDim,
          opacity: tagP,
          display: "flex",
          gap: 20,
          alignItems: "center",
          zIndex: 1,
        }}
      >
        <span>Open source</span>
        <span style={{ color: colors.accent }}>·</span>
        <span>AI Safety Research</span>
      </div>
    </AbsoluteFill>
  );
};
