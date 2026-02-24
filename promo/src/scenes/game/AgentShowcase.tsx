import React from "react";
import { AbsoluteFill, useCurrentFrame, spring, interpolate } from "remotion";
import { colors, fonts } from "../../theme";

const AGENTS = [
  { name: "Paladin", tag: "Cooperative", color: "#00FF88" },
  { name: "Merchant", tag: "Opportunistic", color: "#FF9500" },
  { name: "Illusionist", tag: "Deceptive", color: "#A855F7" },
  { name: "Enforcer", tag: "Hostile", color: "#FF3B5C" },
  { name: "Technomancer", tag: "Adaptive", color: "#00E5FF" },
  { name: "Builder", tag: "Builder", color: "#FACC15" },
];

export const AgentShowcase: React.FC = () => {
  const frame = useCurrentFrame();

  // Title animation
  const titleP = spring({ frame, fps: 30, config: { damping: 200 } });

  return (
    <AbsoluteFill
      style={{
        background: `radial-gradient(ellipse at 50% 40%, ${colors.accentDim}12, ${colors.bg} 70%)`,
        display: "flex",
        flexDirection: "column",
        alignItems: "center",
        justifyContent: "flex-start",
        paddingTop: 180,
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

      {/* Section title */}
      <div
        style={{
          fontSize: 48,
          fontWeight: 700,
          color: colors.textDim,
          letterSpacing: "0.12em",
          opacity: titleP,
          marginBottom: 80,
          textTransform: "uppercase",
        }}
      >
        6 Agent Types
      </div>

      {/* Agent cards */}
      <div
        style={{
          display: "flex",
          flexDirection: "column",
          gap: 36,
          alignItems: "flex-start",
          paddingLeft: 200,
          zIndex: 1,
        }}
      >
        {AGENTS.map((agent, i) => {
          const delay = 20 + i * 25;
          const p = Math.max(
            0,
            spring({ frame: frame - delay, fps: 30, config: { damping: 200 } }),
          );
          const slideX = interpolate(p, [0, 1], [-120, 0]);

          // Gentle idle float
          const floatY = Math.sin(frame * 0.04 + i * 1.5) * 3;

          return (
            <div
              key={agent.name}
              style={{
                display: "flex",
                alignItems: "center",
                gap: 28,
                opacity: p,
                transform: `translateX(${slideX}px) translateY(${floatY}px)`,
              }}
            >
              {/* Agent circle */}
              <div
                style={{
                  width: 64,
                  height: 64,
                  borderRadius: "50%",
                  background: `radial-gradient(circle at 40% 40%, ${agent.color}, ${agent.color}80)`,
                  boxShadow: `0 0 24px ${agent.color}50`,
                  flexShrink: 0,
                }}
              />

              {/* Name + tag */}
              <div style={{ display: "flex", flexDirection: "column", gap: 4 }}>
                <div
                  style={{
                    fontSize: 44,
                    fontWeight: 700,
                    color: colors.text,
                    letterSpacing: "0.04em",
                  }}
                >
                  {agent.name}
                </div>
                <div
                  style={{
                    fontSize: 26,
                    fontFamily: fonts.mono,
                    color: agent.color,
                    letterSpacing: "0.06em",
                  }}
                >
                  {agent.tag}
                </div>
              </div>
            </div>
          );
        })}
      </div>
    </AbsoluteFill>
  );
};
